# Base R power functions against StatClaim's approximate power for cited tests.
# Run from the repository root:
#   Rscript replication/comparison/power_base_r.R
# Needs base R only. It regenerates tests/fixtures/power_r.json, which the tests and
# replication/power.py compare with StatClaim, and writes power_base_r.txt beside this
# file with the values and the R session.
source("tests/fixtures/power_r.R")
sink("replication/comparison/power_base_r.txt")
cat("Base R power values written to tests/fixtures/power_r.json\n")
cat("StatClaim's values for the same cases are in replication/power_results.md\n\n")
cat(readLines("tests/fixtures/power_r.json"), sep = "\n")
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
# R pads printed columns with spaces; drop them at the ends of lines.
output <- "replication/comparison/power_base_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote replication/comparison/power_base_r.txt\n")
