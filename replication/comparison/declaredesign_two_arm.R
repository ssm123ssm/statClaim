# What DeclareDesign reports for a simple two-arm design: simulated diagnosands.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/declaredesign_two_arm.R
# Needs the R package DeclareDesign. Writes declaredesign_two_arm.txt beside this file.
# StatClaim's side is two_arm_power.stat; see statclaim_side.py.
suppressMessages(library(DeclareDesign))
set.seed(20261117)
# 100 per arm, a true difference of 0.4 standard deviations, two-sided 5%.
design <-
  declare_model(N = 200, U = rnorm(N), potential_outcomes(Y ~ 0.4 * Z + U)) +
  declare_inquiry(ATE = mean(Y_Z_1 - Y_Z_0)) +
  declare_assignment(Z = complete_ra(N, m = 100)) +
  declare_measurement(Y = reveal_outcomes(Y ~ Z)) +
  declare_estimator(Y ~ Z, .method = difference_in_means, inquiry = "ATE")
diagnosis <- diagnose_design(design, sims = 2000, bootstrap_sims = 200)

sink("replication/comparison/declaredesign_two_arm.txt")
cat("DeclareDesign: 100 per arm, true difference 0.4 SD, difference in means, two-sided 5%\n\n")
columns <- c("n_sims", "mean_estimand", "mean_estimate", "bias", "sd_estimate", "rmse",
             "power", "se(power)", "coverage", "se(coverage)")
values <- diagnosis$diagnosands_df[, columns]
print(data.frame(diagnosand = columns, value = round(unlist(values), 4)), row.names = FALSE)
cat("\nFor comparison, base R's power.t.test (pooled t-test):",
    sprintf("%.4f", power.t.test(n = 100, delta = 0.4, sd = 1, sig.level = 0.05)$power), "\n\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
# R pads printed columns with spaces; drop them at the ends of lines.
output <- "replication/comparison/declaredesign_two_arm.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote replication/comparison/declaredesign_two_arm.txt\n")
