# Spending boundaries for group_sequential designs, from rpact and gsDesign.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/spending_boundaries_r.R
# Needs rpact, gsDesign and jsonlite. It regenerates tests/fixtures/spending_boundaries_r.json,
# which tests/test_spending_boundaries.py compares with StatClaim offline, and writes
# spending_boundaries_r.txt beside this file with the values and the R session.
#
# StatClaim reads each look's information from its arm sizes, n_c n_t / (n_c + n_t). A
# two-sided design spends half the level on each side, as rpact (sided = 2) and gsDesign
# (test.type = 2) do. The chance of stopping at each look, at a drift theta per unit of
# information, comes from gsDesign::gsProbability with those boundaries.
suppressMessages(library(rpact))
suppressMessages(library(gsDesign))
suppressMessages(library(jsonlite))

cases <- list(
  list(sizes = list(c(50, 50), c(100, 100)), alpha = "1/20", sides = 2, spending = "obrien_fleming",
       drift = 0.5),
  list(sizes = list(c(40, 40), c(80, 80), c(120, 120)), alpha = "1/20", sides = 2,
       spending = "pocock", drift = 0.35),
  list(sizes = list(c(30, 30), c(70, 70), c(100, 100)), alpha = "1/40", sides = 1,
       spending = "obrien_fleming", drift = 0.4),
  list(sizes = list(c(20, 40), c(40, 80), c(60, 120), c(80, 160)), alpha = "1/40", sides = 1,
       spending = "pocock", drift = 0.3)
)

value <- function(text) eval(parse(text = text))
found <- list()
sink("replication/comparison/spending_boundaries_r.txt")
for (case in cases) {
  information <- sapply(case$sizes, function(s) s[1] * s[2] / (s[1] + s[2]))
  rates <- information / information[length(information)]
  type <- if (case$spending == "obrien_fleming") "asOF" else "asP"
  design <- getDesignGroupSequential(informationRates = rates, alpha = value(case$alpha),
                                     sided = case$sides, typeOfDesign = type)
  critical <- design$criticalValues
  nominal <- case$sides * (1 - pnorm(critical))
  lower <- if (case$sides == 2) -critical else rep(-20, length(critical))
  sf <- if (case$spending == "obrien_fleming") sfLDOF else sfLDPocock
  checked <- gsDesign(k = length(rates), test.type = if (case$sides == 2) 2 else 1,
                      alpha = value(case$alpha) / case$sides, beta = 0.2, timing = rates,
                      sfu = sf)
  power <- gsProbability(k = length(rates), theta = case$drift, n.I = information,
                         a = lower, b = critical)
  stop_drift <- power$upper$prob[, 1] + power$lower$prob[, 1]
  null <- gsProbability(k = length(rates), theta = 0, n.I = information, a = lower, b = critical)
  stop_null <- null$upper$prob[, 1] + null$lower$prob[, 1]
  cat(sprintf("%s, %d-sided, alpha %s, looks %s\n", case$spending, case$sides, case$alpha,
              paste(sapply(case$sizes, function(s) sprintf("(%d, %d)", s[1], s[2])), collapse = " ")))
  line <- function(label, values) cat(label, paste(values, collapse = " "), "\n", sep = "")
  line("  rpact critical values:    ", sprintf("%.6f", critical))
  line("  gsDesign critical values: ", sprintf("%.6f", checked$upper$bound))
  line("  nominal levels:           ", sprintf("%.7f", nominal))
  line(sprintf("  stopping at drift %.2f:     ", case$drift), sprintf("%.6f", stop_drift))
  line("  stopping under the null:  ", sprintf("%.6f", stop_null))
  cat("\n")
  found[[length(found) + 1]] <- list(
    sizes = case$sizes, alpha = case$alpha, sides = case$sides, spending = case$spending,
    critical = critical, gsdesign = checked$upper$bound, nominal = nominal,
    drift = case$drift, stopped = stop_drift, stopped_null = stop_null
  )
}
writeLines(toJSON(list(cases = found), digits = 12, auto_unbox = TRUE, pretty = TRUE),
           "tests/fixtures/spending_boundaries_r.json")
cat("R session\n")
info <- sessionInfo()
cat(info$R.version$version.string, "\n", sep = "")
for (pkg in c("rpact", "gsDesign", "jsonlite")) {
  cat(pkg, " ", as.character(packageVersion(pkg)), "\n", sep = "")
}
sink()
