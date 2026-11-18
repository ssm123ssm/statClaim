# What graphicalMCP computes for a graph with recycling, and how it treats invalid graphs.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/graph_graphicalMCP.R
# Needs the R package graphicalMCP. Writes graph_graphicalMCP.txt beside this file.
# StatClaim's side is graph.stat and the files graph_invalid_*.stat; see statclaim_side.py.
suppressMessages(library(graphicalMCP))
set.seed(20261117)
# Three hypotheses: H1 and H2 start with half the level each, H3 with none; a rejected
# hypothesis passes its whole level on, H1 -> H2 -> H3 -> H1.
weights <- c(1 / 2, 1 / 2, 0)
transitions <- rbind(c(0, 1, 0), c(0, 0, 1), c(1, 0, 0))
graph <- graph_create(weights, transitions)

sink("replication/comparison/graph_graphicalMCP.txt")
cat("graphicalMCP on a three-hypothesis graph with recycling, one-sided alpha = 0.025\n\n")
print(graph)
for (p in list(c(0.010, 0.020, 0.005), c(0.020, 0.011, 0.030), c(0.030, 0.030, 0.001))) {
  result <- graph_test_shortcut(graph, p = p, alpha = 0.025)
  cat("\np-values:          ", format(p, nsmall = 3), "\n")
  cat("adjusted p-values: ", format(round(result$outputs$adjusted_p, 4), nsmall = 3), "\n")
  cat("rejected:          ", result$outputs$rejected, "\n")
}
cat("\nPower by simulation (10,000 runs), marginal power 0.9, 0.9, 0.8, independent tests:\n")
power <- graph_calculate_power(graph, alpha = 0.025, power_marginal = c(0.9, 0.9, 0.8),
                               sim_n = 1e4)
print(round(power$power$power_local, 3))
cat("\nInvalid graphs:\n")
invalid <- list(
  "a row of transitions sums to 1.3" = list(weights, rbind(c(0, 0.7, 0.6), c(0, 0, 1),
                                                          c(1, 0, 0))),
  "the weights sum to 1.1" = list(c(0.6, 0.5, 0), transitions),
  "a hypothesis passes level to itself" = list(weights, rbind(c(0.2, 0.8, 0), c(0, 0, 1),
                                                               c(1, 0, 0)))
)
for (name in names(invalid)) {
  message <- tryCatch({
    graph_create(invalid[[name]][[1]], invalid[[name]][[2]])
    "accepted"
  }, error = function(e) conditionMessage(e))
  cat(sprintf("  %s: %s\n", name, message))
}
cat("\n")
print(sessionInfo(), locale = FALSE)  # leave out the locale and time zone
sink()
# R pads printed columns with spaces; drop them at the ends of lines.
output <- "replication/comparison/graph_graphicalMCP.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote replication/comparison/graph_graphicalMCP.txt\n")
