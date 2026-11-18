# Compare StatClaim's re-check of Simon (1989) with clinfun::ph2simon.
# Run from the repository root:
#   R_LIBS_USER=path/to/library Rscript replication/comparison/simon_clinfun.R
# Needs the R packages clinfun and jsonlite. Writes simon_clinfun.txt beside this file.
suppressMessages({
  library(clinfun)
  library(jsonlite)
})
designs <- fromJSON("replication/simon1989.json")$designs
statclaim <- fromJSON("replication/simon_results.json")
fraction <- function(text) {
  parts <- as.numeric(strsplit(text, "/")[[1]])
  if (length(parts) == 2) parts[1] / parts[2] else parts
}
label <- function(r1, n1, r, n) sprintf("%d/%d, %d/%d", r1, n1, r, n)

rows <- list()
settings <- unique(designs[, c("p0", "p1", "alpha", "beta")])
for (i in seq_len(nrow(settings))) {
  s <- settings[i, ]
  # StatClaim's search covers designs of up to 120 participants; use the same limit.
  fit <- ph2simon(as.numeric(s$p0), as.numeric(s$p1), fraction(s$alpha), fraction(s$beta),
                  nmax = 120)
  picks <- list(minimax = fit$xopt[1, ], optimal = fit$xopt[nrow(fit$xopt), ])
  for (kind in names(picks)) {
    j <- which(designs$kind == kind & designs$p0 == s$p0 & designs$p1 == s$p1 &
                 designs$alpha == s$alpha & designs$beta == s$beta)
    d <- designs[j, ]
    sc <- statclaim[j, ]
    pick <- picks[[kind]]
    rows[[length(rows) + 1]] <- data.frame(
      kind = kind, p0 = s$p0, p1 = s$p1, alpha = s$alpha, beta = s$beta,
      simon = label(d$r1, d$n1, d$r, d$n),
      clinfun = label(pick["r1"], pick["n1"], pick["r"], pick["n"]),
      simon_en = d$en, clinfun_en = unname(pick["EN(p0)"]), statclaim_en = sc$expected_size,
      simon_pet = d$pet, clinfun_pet = unname(pick["PET(p0)"]), statclaim_pet = sc$early_stop
    )
  }
}
table <- do.call(rbind, rows)
same_design <- table$simon == table$clinfun
en_agree <- abs(table$clinfun_en - table$statclaim_en) < 5e-3
pet_agree <- abs(table$clinfun_pet - table$statclaim_pet) < 5e-5
printed_pet_differs <- abs(table$simon_pet - table$statclaim_pet) >= 0.005

sink("replication/comparison/simon_clinfun.txt")
cat("clinfun::ph2simon against StatClaim's re-check of Simon (1989)\n\n")
cat(sprintf("Designs compared: %d (optimal and minimax for %d settings), nmax = 120\n",
            nrow(table), nrow(settings)))
cat(sprintf("clinfun selects the tabulated design: %d of %d\n", sum(same_design), nrow(table)))
cat(sprintf("Expected size under p0 agrees with StatClaim to 0.005: %d of %d\n",
            sum(en_agree), nrow(table)))
cat(sprintf("Early-stopping probability agrees with StatClaim to 0.00005: %d of %d\n",
            sum(pet_agree), nrow(table)))
cat(sprintf("Printed PET in Simon's tables differs from both by 0.005 or more: %d\n\n",
            sum(printed_pet_differs & pet_agree)))
cat("Designs where clinfun selects another design:\n")
print(table[!same_design, c("kind", "p0", "p1", "alpha", "beta", "simon", "clinfun",
                            "clinfun_en", "statclaim_en")], row.names = FALSE)
cat("\nPrinted PET values that differ (Simon's table, clinfun, StatClaim):\n")
print(table[printed_pet_differs, c("kind", "p0", "p1", "alpha", "beta", "simon",
                                   "simon_pet", "clinfun_pet", "statclaim_pet")],
      row.names = FALSE)
cat("\nAll designs:\n")
options(width = 200)
print(within(table, {
  clinfun_en <- round(clinfun_en, 3); statclaim_en <- round(statclaim_en, 3)
  clinfun_pet <- round(clinfun_pet, 4); statclaim_pet <- round(statclaim_pet, 4)
}), row.names = FALSE)
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
# R pads printed columns with spaces; drop them at the ends of lines.
output <- "replication/comparison/simon_clinfun.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote replication/comparison/simon_clinfun.txt\n")
