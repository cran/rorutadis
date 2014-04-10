\name{investigateUtility}
\alias{investigateUtility}
\title{Post factum analysis: check how much utility is missing}
\usage{
investigateUtility(alternative, atLeastToClass, necessary, problem)
}
\arguments{
  \item{alternative}{An alternative index.}

  \item{atLeastToClass}{An assignment to investigate.}

  \item{necessary}{Whether necessary or possible assignment
  is considered.}

  \item{problem}{Problem for investigation.}
}
\value{
List with named elements: \itemize{ \item \code{ux} - value
of missing utility, \item \code{solution} - result of
solving model. It can be used for further computations
(e.g. \code{\link{getThresholds}},
\code{\link{getMarginalUtilities}},
\code{\link{getCharacteristicPoints}}). } \code{NULL} is
returned if given assignment is not possible.
}
\description{
This function calculates missing value of an alternative
utility for that alternative to be possibly (or
necessarily) assigned to at least some specific class.
}
\examples{
perf <- matrix(c(8, 2, 1, 7, 0.5, 0.9, 0.4, 0.5), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
problem <- addAssignmentsUB(problem, c(1, 2), c(2, 3))

result <- investigateUtility(4, 3, FALSE, problem)
}
\seealso{
\code{\link{getMarginalUtilities}}
\code{\link{getCharacteristicPoints}}
\code{\link{getThresholds}} \code{\link{improveAssignment}}
}

