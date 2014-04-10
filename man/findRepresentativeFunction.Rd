\name{findRepresentativeFunction}
\alias{findRepresentativeFunction}
\title{Find representative utility function}
\usage{
findRepresentativeFunction(problem, mode)
}
\arguments{
  \item{problem}{Problem to investigate.}

  \item{mode}{An integer that represents a method of a
  computing representative utility function: \itemize{
  \item \code{0} - iterative mode, \item \code{1} -
  compromise mode. }}
}
\value{
This function returns a result of solving model of a
problem. It can be used for further computations (e.g.
\code{\link{getThresholds}},
\code{\link{getMarginalUtilities}},
\code{\link{getCharacteristicPoints}}). If representative
utility function was not found, the function returns
\code{NULL}.
}
\description{
This function finds a representative utility function for a
problem.
}
\examples{
perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))

representativeFunction <- findRepresentativeFunction(problem, 0)
thresholds <- getThresholds(problem, representativeFunction)
}
\seealso{
\code{\link{getCharacteristicPoints}}
\code{\link{getMarginalUtilities}}
\code{\link{getThresholds}}
}

