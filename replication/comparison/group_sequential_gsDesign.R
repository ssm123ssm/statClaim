# How conservative is StatClaim's union-bound split of alpha across looks?
# Compares it with gsDesign's boundaries, which use the correlation between looks.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/group_sequential_gsDesign.R
# Needs the R package gsDesign. Writes group_sequential_gsDesign.txt beside this file.
# StatClaim's side is sequential.stat; see statclaim_side.py.
suppressMessages(library(gsDesign))
timing <- c(1 / 2, 1)
alpha <- 0.025

# Probability of crossing an upper boundary at drift theta. The lower boundaries are
# placed far away, so the study stops only to reject.
crossing <- function(bounds, theta = 0, information = timing) {
  sum(gsProbability(k = 2, theta = theta, n.I = information, a = c(-20, -20),
                    b = bounds)$upper$prob)
}

sink("replication/comparison/group_sequential_gsDesign.txt")
cat("Two looks, at half and all of the information; one-sided alpha = 0.025.\n")
cat("Each union-bound split tests look k at nominal level alpha_k, with the alpha_k\n")
cat("summing to 0.025. That is what StatClaim's alpha_spending declares and checks.\n\n")
for (spending in list(list(name = "O'Brien-Fleming type (Lan-DeMets)", sf = sfLDOF),
                      list(name = "Pocock type (Lan-DeMets)", sf = sfLDPocock))) {
  design <- gsDesign(k = 2, test.type = 1, alpha = alpha, beta = 0.1, timing = timing,
                     sfu = spending$sf)
  spent <- design$upper$spend
  exact <- design$upper$bound
  split <- qnorm(1 - spent)  # the same spending, but each look at its own share
  cat(spending$name, "spending\n")
  cat(sprintf("  alpha spent at each look:         %.6f %.6f\n", spent[1], spent[2]))
  cat(sprintf("  gsDesign boundaries (z):          %.4f %.4f; nominal levels %.6f %.6f\n",
              exact[1], exact[2], pnorm(-exact[1]), pnorm(-exact[2])))
  cat(sprintf("  union-bound boundaries (z):       %.4f %.4f; nominal levels %.6f %.6f\n",
              split[1], split[2], spent[1], spent[2]))
  cat(sprintf("  true Type I error, gsDesign:      %.6f\n", crossing(exact)))
  cat(sprintf("  true Type I error, union bound:   %.6f (bound claimed: %.3f)\n",
              crossing(split), alpha))
  cat(sprintf("  power where gsDesign has 90%%:     gsDesign %.4f, union bound %.4f\n\n",
              crossing(exact, design$delta, design$n.I),
              crossing(split, design$delta, design$n.I)))
}
cat("The split StatClaim's example declares: 0.0015 at the first look, 0.0235 at the end.\n")
fixed_split <- qnorm(1 - c(0.0015, 0.0235))
cat(sprintf("  true Type I error: %.6f (bound claimed: 0.025)\n\n", crossing(fixed_split)))
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
# R pads printed columns with spaces; drop them at the ends of lines.
output <- "replication/comparison/group_sequential_gsDesign.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote replication/comparison/group_sequential_gsDesign.txt\n")
