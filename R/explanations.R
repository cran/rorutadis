#### EXPLANATIONS HELPERS

isSuperset <- function(set, subset) {
  for (i in subset)
    if (!(i %in% set))
      return (FALSE)
  return (TRUE)
}

#### EXPLANATIONS

explainAssignmentQuickly <- function(alternative, fromClass, toClass, problem,
                              baseModel = NULL, restrictionIndices = NULL,
                              altVars = NULL, epsilonIndex = NULL,
                              firstThresholdIndex = NULL, lastThresholdIndex = NULL) {
  stopifnot(fromClass >= 1)
  stopifnot(toClass >= 1)
  stopifnot(fromClass <= problem$nrClasses)
  stopifnot(toClass <= problem$nrClasses)
  
  if (is.null(baseModel))
    baseModel <- buildBaseModel(problem)
  if (is.null(restrictionIndices))
    restrictionIndices <- buildBaseModel(problem, FALSE, TRUE)
  
  if (is.null(epsilonIndex))
    epsilonIndex <- getEpsilonIndex(problem)
  
  if (is.null(altVars)) {
    altVars <- buildAltVariableMatrix(problem$perf)
    for (i in 1:(ncol(baseModel$lhs) - epsilonIndex))
      altVars <- cbind(altVars, 0)
  }
  
  if (is.null(firstThresholdIndex))
    firstThresholdIndex <- getFirstThresholdIndex(problem)
  
  if (is.null(lastThresholdIndex))
    lastThresholdIndex <- getLastThresholdIndex(problem)
  
  addConst <- c()
  allConst <- baseModel
  
  if (fromClass == 1 && toClass < problem$nrClasses) {
    addConst <- buildLBAssignmentsConstraint(alternative,
                                             toClass + 1,
                                             altVars,
                                             firstThresholdIndex,
                                             lastThresholdIndex)
    allConst <- combineConstraints(allConst, addConst)
  }
  else if (fromClass > 1 && toClass == problem$nrClasses) {
    addConst <- buildUBAssignmentsConstraint(alternative,
                                             fromClass - 1,
                                             altVars,
                                             firstThresholdIndex,
                                             lastThresholdIndex,
                                             epsilonIndex)
    allConst <- combineConstraints(allConst, addConst)
  }
  else if (fromClass > 1 && toClass < problem$nrClasses) {
    addConst1 <- buildLBAssignmentsConstraint(alternative,
                                              toClass + 1,
                                              altVars,
                                              firstThresholdIndex,
                                              lastThresholdIndex)
    addConst2 <- buildUBAssignmentsConstraint(alternative,
                                              fromClass - 1,
                                              altVars,
                                              firstThresholdIndex,
                                              lastThresholdIndex,
                                              epsilonIndex)
    addConst3 <- list(lhs = rep(0, ncol(allConst$lhs)), dir = "==", rhs = 1)# this constraint is filled ~10 loc below
    allConst <- combineConstraints(allConst, addConst1, addConst2, addConst3)
    
    allConst$lhs <- cbind(allConst$lhs, 0)
    allConst$lhs <- cbind(allConst$lhs, 0)
    allConst$types <- c(allConst$types, "B")
    allConst$types <- c(allConst$types, "B")
    
    lhsdim <- dim(allConst$lhs)
    allConst$lhs[lhsdim[1] - 2, lhsdim[2] - 1] <- RORUTADIS_BIGM
    allConst$lhs[lhsdim[1] - 1, lhsdim[2]] <- -RORUTADIS_BIGM
    allConst$lhs[lhsdim[1], lhsdim[2] - 1] <- 1
    allConst$lhs[lhsdim[1], lhsdim[2]] <- 1
  }
  
  nrRestrictions <- length(restrictionIndices) / 2
  
  if (nrRestrictions == 0) {
    if (isModelConsistent(model, epsilonIndex))
      return (list())
    else
      return (NULL)
  }
  
  subsets <- lapply(1:nrRestrictions, function(x) combn(nrRestrictions, x))
  
  preferentialReducts <- list()
  
  constraintsToRemove <- removeConstraintsByRestrictions(restrictionIndices, c())
  model <- removeConstraints(allConst, constraintsToRemove)
  
  if (!isModelConsistent(model, epsilonIndex))
    return (NULL)

  for (i in 1:length(subsets)) {
    for (j in 1:ncol(subsets[[i]])) {
      subset <- subsets[[i]][, j]
      if (subset[1] > 0) {
        constraintsToRemove <- removeConstraintsByRestrictions(restrictionIndices, subset)
        if (!is.null(constraintsToRemove))
          model <- removeConstraints(allConst, constraintsToRemove)
        
        if (!isModelConsistent(model, epsilonIndex)) {
          preferentialReducts[[length(preferentialReducts) + 1]] <- subset
          for (k in 1:length(subsets)) {
            for (l in 1:ncol(subsets[[k]])) {
              if (isSuperset(subsets[[k]][, l], subset)) {
                subsets[[k]][1, l] <- 0
              }
            }
          }
        }
      }
    }
  }
  
  return (preferentialReducts)
}

#' Explain assignment
#'
#' This function allows to obtain explanation of an alternative assignment to
#' a specific class interval or one class in case if assignment is necessary.
#' The function returns all preferential reducts for an assignment relation.
#'
#' @param alternative Index of an alternative.
#' @param classInterval Two-element vector \code{c(l, u)} that represents
#' an assignment of \code{alternative} to class interval \code{[C_l, C_u]}
#' (\code{l <= u}). 
#' @param problem Problem for which computations will be performed.
#' @return List of all preferential reducts for an assignment relation
#' or \code{NULL} if an assignment is not influenced by restrictions.
#' Each element of that list is a preferential reduct represented as a vector
#' of restriction indices. To identify preferential core use
#' \code{\link{getPreferentialCore}}.
#' To find out about restrictions by their indices use \code{\link{getRestrictions}}.
#' If there was not possible to find explanations the function will return \code{NULL}.
#' @seealso
#' \code{\link{getPreferentialCore}}
#' \code{\link{getRestrictions}}
#' \code{\link{calculateAssignments}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.5), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' possibleAssignments <- calculateAssignments(problem, FALSE)
#' alternative <- 4
#' assignment <- c(min(which(possibleAssignments[alternative, ])),
#'                max(which(possibleAssignments[alternative, ])))
#'                
#' preferentialReducts <- explainAssignment(alternative,
#'    assignment, problem)
#' preferentialCore <- getPreferentialCore(preferentialReducts)
#' coreRestrictions <- getRestrictions(problem, preferentialCore)
#' @export
explainAssignment <- function(alternative, classInterval, problem) {
  stopifnot(is.vector(classInterval))
  stopifnot(length(classInterval) == 2)
  stopifnot(classInterval[1] <= classInterval[2])
  return (explainAssignmentQuickly(alternative, classInterval[1], classInterval[2], problem))
}

#' Identify preferential core
#'
#' This function identifies preferential core.
#'
#' @param preferentialReducts List of all preferential reducts 
#' (a result of \code{\link{explainAssignment}}).
#' @return Preferential core as a vector of restriction indices.
#' To find out about restrictions by their indices use \code{\link{getRestrictions}}.
#' @seealso
#' \code{\link{explainAssignment}}
#' \code{\link{getRestrictions}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.5), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' possibleAssignments <- calculateAssignments(problem, FALSE)
#' alternative <- 4
#' assignment <- c(min(which(possibleAssignments[alternative, ])),
#'                max(which(possibleAssignments[alternative, ])))
#'                
#' preferentialReducts <- explainAssignment(alternative,
#'    assignment, problem)
#' preferentialCore <- getPreferentialCore(preferentialReducts)
#' coreRestrictions <- getRestrictions(problem, preferentialCore)
#' @export
getPreferentialCore <- function(preferentialReducts) {
  if (length(preferentialReducts) == 0) {
    return (c())
  }
  else if (length(preferentialReducts) == 1) {
    return (preferentialReducts[[1]])
  }
  
  res <- preferentialReducts[[1]]
  
  for (i in 2:length(preferentialReducts)) {
    oldRes <- res
    res <- c()
    for (j in 1:length(oldRes)) {
      if (oldRes[j] %in% preferentialReducts[[i]]) {
        res <- c(res, oldRes[j])
      }
    }
  }
  
  return (res)
}
