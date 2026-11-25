# A search over the sizes of two looks of Fisher's test, done independently in R.
# Run from the repository root:
#   R_LIBS=path/to/library Rscript replication/comparison/look_sizes_r.R
# Needs jsonlite. It regenerates tests/fixtures/look_sizes_r.json, which
# tests/test_look_search.py compares with StatClaim offline, and writes look_sizes_r.txt
# beside this file.
#
# Every choice of an interim and a final size per arm on the grid is a candidate, each look at
# its declared level. Each look's rejection region comes from fisher.test on every table; the
# chance of stopping at each look sums dbinom products over every path of counts. The minimax
# design has the smallest final size among those with the target power, then the smallest
# expected total; the optimal design has the smallest expected total.
suppressMessages(library(jsonlite))

value <- function(text) eval(parse(text = text))
region <- function(n, level) {
  rejects <- matrix(FALSE, n + 1, n + 1)
  for (x_c in 0:n) for (x_t in 0:n) {
    table <- matrix(c(x_t, x_c, n - x_t, n - x_c), nrow = 2)
    rejects[x_c + 1, x_t + 1] <- fisher.test(table)$p.value <= level
  }
  rejects
}
stopping <- function(n1, n2, p_c, p_t, levels) {
  first <- region(n1, levels[1])
  second <- region(n2, levels[2])
  m <- n2 - n1
  stop1 <- 0
  stop2 <- 0
  for (x_c in 0:n1) for (x_t in 0:n1) {
    w <- dbinom(x_c, n1, p_c) * dbinom(x_t, n1, p_t)
    if (first[x_c + 1, x_t + 1]) {
      stop1 <- stop1 + w
      next
    }
    for (a in 0:m) for (b in 0:m) {
      if (second[x_c + a + 1, x_t + b + 1]) {
        stop2 <- stop2 + w * dbinom(a, m, p_c) * dbinom(b, m, p_t)
      }
    }
  }
  c(stop1, stop2)
}

grid <- seq(6, 42, by = 6)
levels <- c(value("1/100"), value("1/25"))
p_c <- value("3/10")
p_t <- value("7/10")
minimum <- value("4/5")
candidates <- list()
for (i in seq_along(grid)) for (j in seq_along(grid)) {
  if (j <= i) next
  n1 <- grid[i]
  n2 <- grid[j]
  stopped <- stopping(n1, n2, p_c, p_t, levels)
  expected <- stopped[1] * 2 * n1 + (1 - stopped[1]) * 2 * n2
  candidates[[length(candidates) + 1]] <- list(
    looks = c(n1, n2), stopped = stopped, power = sum(stopped), expected = expected
  )
}
feasible <- Filter(function(c) c$power >= minimum, candidates)
finals <- sapply(feasible, function(c) c$looks[2])
expected <- sapply(feasible, function(c) c$expected)
minimax <- feasible[[order(finals, expected)[1]]]$looks
optimal <- feasible[[order(expected, finals)[1]]]$looks

writeLines(toJSON(list(grid = grid, levels = c("1/100", "1/25"), p_control = "3/10",
                       p_treatment = "7/10", minimum = "4/5", candidates = candidates,
                       minimax = minimax, optimal = optimal),
                  auto_unbox = TRUE, digits = NA, pretty = TRUE),
           "tests/fixtures/look_sizes_r.json")
sink("replication/comparison/look_sizes_r.txt")
cat("Two looks of Fisher's test at levels 1/100 and 1/25, rates 3/10 and 7/10, grid", grid, "\n")
for (c in candidates) {
  cat(sprintf("looks (%d, %d): stopping %.12f, %.12f; power %.6f; expected total %.4f\n",
              c$looks[1], c$looks[2], c$stopped[1], c$stopped[2], c$power, c$expected))
}
cat(sprintf("\nminimax design: (%d, %d) per arm\noptimal design: (%d, %d) per arm\n\n",
            minimax[1], minimax[2], optimal[1], optimal[2]))
print(sessionInfo(), locale = FALSE)
sink()
output <- "replication/comparison/look_sizes_r.txt"
writeLines(sub("[ \t]+$", "", readLines(output)), output)
cat("Wrote", output, "\n")
