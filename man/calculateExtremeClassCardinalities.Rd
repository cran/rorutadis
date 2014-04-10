\name{calculateExtremeClassCardinalities}
\alias{calculateExtremeClassCardinalities}
\title{Calculate extreme class cardinalities}
\usage{
calculateExtremeClassCardinalities(problem)
}
\arguments{
  \item{problem}{Problem for which extreme class
  cardinalities will be calculated.}
}
\value{
\emph{p} x \emph{2} matrix, where \emph{p} is the number of
classes. Value at \code{[h, 1]} is a minimal possible
cardinality of class \code{C_h}, and value at \code{[h, 2]}
is a maximal possible cardinality of class \code{C_h}.
}
\description{
This function calculates minimal and maximal possible
cardinality of each class.
}
\examples{
perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))

extremeClassCardinalities <- calculateExtremeClassCardinalities(problem)
}

