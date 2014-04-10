\name{removeAssignmentPairwiseAtMostComparisons}
\alias{removeAssignmentPairwiseAtMostComparisons}
\title{Remove assignment pairwise \emph{at most} comparisons}
\usage{
removeAssignmentPairwiseAtMostComparisons(problem, ...)
}
\arguments{
  \item{problem}{Problem from which preference information
  will be removed}

  \item{...}{Comparisons as three-element vectors and/or
  two-element vectors. Each argument represents comparison
  to remove. If \code{c(i, j, k)} vector was provided a
  corresponding comparison will be removed. In case where
  two-element vector \code{c(i,j)} was given a comparison
  of an alternative \emph{a_i} with \emph{a_j} will be
  removed regardless of value of \emph{k}. If a specific
  comparison was not found nothing will happen.}
}
\value{
Problem with removed comparisons.
}
\description{
This function removes pairwise \emph{at most} comparisons.
For more information see
\code{addPairwiseAtMostComparisons}.
}
\examples{
# 4 alternatives, 2 gain criteria, 3 classes, monotonously increasing
# and general marginal value functions
perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))

# add comparison:
# alternative 4 to class at most better by 1 class then class
# of alternative 3
problem <- addAssignmentPairwiseAtMostComparisons(problem, c(4, 3, 1))
# remove comparison between alternative 4 and 3
problem <- removeAssignmentPairwiseAtMostComparisons(problem, c(4, 3))
}

