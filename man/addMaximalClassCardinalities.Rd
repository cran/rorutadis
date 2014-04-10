\name{addMaximalClassCardinalities}
\alias{addMaximalClassCardinalities}
\title{Add maximal class cardinality restrictions}
\usage{
addMaximalClassCardinalities(problem, ...)
}
\arguments{
  \item{problem}{Problem to which preference information
  will be added.}

  \item{...}{Minimal cardinalities as two-element vectors
  \code{c(i, j)}, where \emph{j} is a maximal cardinality
  of class \emph{C_i}.}
}
\value{
Problem with added preference information.
}
\description{
This function allows to define maximal cardinality of
particular classes.
}
\examples{
# 4 alternatives, 2 gain criteria, 3 classes, monotonously increasing
# and general marginal value functions
perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))

# set maximal class cardinalities:
# at most two alternatives could be assigned to class 2
# and at most one alternative could be assigned to class 3
problem <- addMaximalClassCardinalities(problem, c(2, 2), c(3, 1))
}
\seealso{
\code{\link{buildProblem}}
\code{\link{removeMaximalClassCardinalities}}
}

