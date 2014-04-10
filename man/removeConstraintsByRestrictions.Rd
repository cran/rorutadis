\name{removeConstraintsByRestrictions}
\alias{removeConstraintsByRestrictions}
\title{Remove constraints indices by restriction indices}
\usage{
removeConstraintsByRestrictions(constraintIntervalIndices,
  restrictionToRemoveIndices)
}
\arguments{
  \item{constraintIntervalIndices}{Vector of interval
  indices of each restriction constraints. c(a_1, b_1, ...,
  a_n, b_n), where i-th of n restrictions is represented as
  model constraints at indices between a_i and b_i
  including a_i, b_i.}

  \item{restrictionToRemoveIndices}{Vector of indices of
  restrictions to remove.}
}
\value{
Vector of model constraints of restrictions which are NOT
in restrictionToRemoveIndices.
}
\description{
This function allows to remove constraints indices from
indices interval by restriction indices.
}

