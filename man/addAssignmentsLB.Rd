\name{addAssignmentsLB}
\alias{addAssignmentsLB}
\title{Add lower bound of alternative possible assignments}
\usage{
addAssignmentsLB(problem, ...)
}
\arguments{
  \item{problem}{Problem to which preference information
  will be added.}

  \item{...}{Assignments as two-element vectors. Each
  vector \code{c(i, j)} represents assignment of an
  alternative \emph{a_i} to class at least as good as class
  \emph{C_j}.}
}
\value{
Problem with added assignment examples.
}
\description{
This function adds lower bounds of possible assignments to
a problem.
}
\examples{
# 4 alternatives, 2 gain criteria, 3 classes, monotonously increasing
# and general marginal value functions
perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))

# add assignment examples: alternative 1 to class at least as good as class 2
# and alternative 2 to class at least as good as class 3
problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
}
\seealso{
\code{\link{buildProblem}}
\code{\link{removeAssignmentsLB}}
}

