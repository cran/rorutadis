\name{addAssignmentPairwiseAtMostComparisons}
\alias{addAssignmentPairwiseAtMostComparisons}
\title{Add assignment pairwise \emph{at most} comparisons}
\usage{
addAssignmentPairwiseAtMostComparisons(problem, ...)
}
\arguments{
  \item{problem}{Problem to which preference information
  will be added.}

  \item{...}{Comparisons as three-element vectors. Each
  vector \code{c(i, j, k)} represents a single assignment
  comparison: alternative \emph{a_i} has to be assigned to
  class at most better by \emph{k} classes then class of
  \emph{a_j}.}
}
\value{
Problem with added comparisons.
}
\description{
The comparison of a pair of alternatives may indicate that
alternative \emph{a_i} should be assigned to a class at
most better by \emph{k} classes then class of \emph{a_j}.
The function \code{assignmentPairwiseAtMostComparisons}
allows to define such pairwise comparisons.
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
}
\seealso{
\code{\link{buildProblem}}
\code{\link{removeAssignmentPairwiseAtMostComparisons}}
}

