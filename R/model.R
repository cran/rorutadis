#### INDICES, NUMBER OF VARIABLES ETC.

getNrAlt <- function(problem) {
  return (nrow(problem$perf))
}

getNrAltVars <- function(problem) {
  return (sum(as.numeric(lapply(getLevels(problem$perf), length))))
}

getEpsilonIndex <- function(problem) {
  return (getNrAltVars(problem) + 1)
}

getFirstCharacteristicPointIndex <- function(problem) {
  if (sum(getNrLinearSegments(problem$characteristicPoints)) == 0)
    stop("There is no characteristic points in this problem.")
  return (getEpsilonIndex(problem) + 1)
}

getFirstThresholdIndex <- function(problem) {
  return (getEpsilonIndex(problem) + sum(getNrLinearSegments(problem$characteristicPoints)) + 1)
}

getLastThresholdIndex <- function(problem) {
  return (getFirstThresholdIndex(problem) + problem$nrClasses - 2)
}

getNrPairAtLeastCompVars <- function(nrClasses, assignmentPairwiseAtLeastComparisons) {
  if (!is.null(assignmentPairwiseAtLeastComparisons)) {
    return (sum(nrClasses - assignmentPairwiseAtLeastComparisons[, 3]))
  }
  else {
    return (0)
  }
}

getNrPairAtMostCompVars <- function(nrClasses, assignmentPairwiseAtMostComparisons) {
  if (!is.null(assignmentPairwiseAtMostComparisons)) {
    return (sum(nrClasses - assignmentPairwiseAtMostComparisons[, 3]))
  }
  else {
    return (0)
  }
}

getNrPairCompBinVars <- function(problem) {
  return (getNrPairAtLeastCompVars(problem$nrClasses,
                                   problem$assignmentPairwiseAtLeastComparisons)
          + getNrPairAtMostCompVars(problem$nrClasses,
                                    problem$assignmentPairwiseAtMostComparisons))
}

getFirstPairCompBinVarIndex <- function(problem) {
  if (getNrPairCompBinVars(problem) == 0)
    stop("There is no pairwice comparisons in this problem.")
  return (getLastThresholdIndex(problem) + 1)
}

getLastPairCompBinVarIndex <- function(problem) {
  return (getFirstPairCompBinVarIndex(problem) + getNrPairCompBinVars(problem) - 1)
}

getFirstClAsgnBinVarIndex <- function(problem) {
  return (getLastThresholdIndex(problem) + getNrPairCompBinVars(problem) + 1)
}

getLastClAsgnBinVarIndex <- function(problem) {
  return (getLastThresholdIndex(problem) + getNrPairCompBinVars(problem) +
            problem$nrClasses * nrow(problem$perf))
}
#### BUILDING MODEL HELPERS

getLevels <- function(perf) {
  res <- list()
  for (i in 1:ncol(perf)) {
    res[[i]] <- sort(unique(perf[, i]))
  }
  return (res)
}

getNrVars <- function(levels) {
  return (sum(as.numeric(lapply(levels, length))) + 1)# + 1 for epsilon
}

getOffsets <- function(levels) {
  x <- cumsum(lapply(levels, length))
  return (c(1, x[1:length(x) - 1] + 1))
}

buildAltVariableMatrix <- function(perf) {
  levels <- getLevels(perf)
  offsets <- getOffsets(levels)
  nrAlts <- nrow(perf)
  nrCrit <- ncol(perf)
  nrVars <- getNrVars(levels)
  
  resMat <- matrix(nrow = nrAlts, ncol = nrVars)
  
  for (i in seq_len(nrAlts)) {
    vec <- array(0, dim = nrVars)
    indices <- sapply(1:nrCrit, function(x) { which(levels[[x]] == perf[i, x]) })
    vec[indices + offsets - 1] <- 1
    resMat[i, ] <- vec
  }
  
  return (resMat)
}

addVarialbesToModel <- function(model, variables) {
  for (var in variables)
    model$lhs <- cbind(model$lhs, 0)
  model$types <- c(model$types, variables)
  return (model)
}

getEvaluation <- function(perf, altVars, level, indexOfVar) {
  for (i in seq_len(nrow(altVars))) {
    if (altVars[i, indexOfVar] == 1) {
      return (perf[i, level])
    }
  }
  
  stop("Invalid arguments.")
}


#### BUILDING CONSTRAINS FOR MODEL HELPERS

###### MONOTONOUS, NORMLIZATION, EPSILON > 0

buildFirstLevelZeroConstraints <- function(perf, criteria) {
  levels <- getLevels(perf)
  offsets <- getOffsets(levels)
  nrVars <- getNrVars(levels)
  
  res <- matrix(0, nrow = length(offsets), ncol = nrVars)
  
  for (i in seq_len(length(offsets))) {
    if (criteria[i] == 'g')
      res[i, offsets[i]] <- 1
    else
      res[i, offsets[i] + length(levels[[i]]) - 1] <- 1
  }
  
  return (list(lhs = res,
               dir = rep("==", length(offsets)),
               rhs = rep(0, length(offsets))))
}

buildBestLevelsAddToUnityConstraint <- function(perf, criteria) {
  levels <- getLevels(perf)
  offsets <- getOffsets(levels)
  nrVars <- getNrVars(levels)
  
  lhs <- rep(0, nrVars)
  ind <- c((offsets - 1)[-1], nrVars - 1)
  
  for (i in seq_len(length(offsets))) {
    if (criteria[i] == 'g')
      lhs[offsets[i] + length(levels[[i]]) - 1] <- 1
    else
      lhs[offsets[i]] <- 1
  }
  
  return (list(lhs = lhs, dir = "==", rhs = 1))
}

buildEpsilonStrictlyPositiveConstraint <- function(nrVars, epsilonIndex) {
  lhs <- rep(0, nrVars)
  lhs[epsilonIndex] <- 1
  return (list(lhs = lhs, dir = ">=", rhs = RORUTADIS_MINEPS))
}

buildMonotonousAndCharacteristicPointsConstraints <- function(perf,
                                                              criteria,
                                                              characteristicPoints,
                                                              strictVF) {  
  levels <- getLevels(perf)
  offsets <- getOffsets(levels)
  epsilonIndex <- getNrVars(levels)
  linearSegments <- getNrLinearSegments(characteristicPoints)
  nrOutputVars <- epsilonIndex + sum(linearSegments)
  firstCharacteristicPointIndex <- epsilonIndex + 1
  altVars <- buildAltVariableMatrix(perf)
  
  resLhs <- c()
  resDir <- c()
  resRhs <- c()
  
  for (i in seq_len(length(levels))) {
    if (linearSegments[i] == 0) {
      for (j in seq_len(length(levels[[i]]) - 1)) {
        index <- offsets[i] + j - 1        
        lhs <- array(0, dim = nrOutputVars)
        lhs[index] <- 1
        lhs[index + 1] <- -1
        if (criteria[i] == 'g') {
          if (strictVF == TRUE) {
            lhs[epsilonIndex] <- 1
          }
          resDir <- c(resDir, "<=")
        }
        else {
          if (strictVF == TRUE) {
            lhs[epsilonIndex] <- -1
          }
          resDir <- c(resDir, ">=")
        }
        
        resLhs <- rbind(resLhs, lhs)
        resRhs <- c(resRhs, 0)
      }
    }
    else {
      # monotonous of characteristic points
      
      lhs <- array(0, dim = nrOutputVars)
      
      if (criteria[i] == 'g') {
        lhs[firstCharacteristicPointIndex] <- 1
      }
      else {
        lhs[firstCharacteristicPointIndex + linearSegments[i] - 1] <- 1
      }
      
      if (strictVF == TRUE) {
        lhs[epsilonIndex] <- -1
      }
      
      resDir <- c(resDir, ">=")
      resLhs <- rbind(resLhs, lhs)
      resRhs <- c(resRhs, 0)
      
      if (linearSegments[i] > 1) {
        for (k in 0:(linearSegments[i]-2)) {
          lhs <- array(0, dim = nrOutputVars)
          lhs[firstCharacteristicPointIndex + k] <- 1
          lhs[firstCharacteristicPointIndex + k + 1] <- -1
          if (criteria[i] == 'g') {
            if (strictVF == TRUE) {
              lhs[epsilonIndex] <- 1
            }
            resDir <- c(resDir, "<=")
          }
          else {
            if (strictVF == TRUE) {
              lhs[epsilonIndex] <- -1
            }
            resDir <- c(resDir, ">=")
          }
          resLhs <- rbind(resLhs, lhs)
          resRhs <- c(resRhs, 0)
        }
      }
      
      maximum <- max(perf[, i])
      minimum <- min(perf[, i])
      
      if (criteria[i] == 'g') {
        for (j in seq_len(length(levels[[i]]) - 1)) {
          index <- offsets[i] + j
          
          x <- getEvaluation(perf, altVars, i, index)
          
          for (k in seq_len(linearSegments[i])) {
            segmentUpperBound <- minimum + (((maximum - minimum) * k) / linearSegments[i])
            
            if (x > segmentUpperBound && k == linearSegments[i]) {
              segmentUpperBound <- maximum
            }
            
            if (x <= segmentUpperBound) {
              segmentLowerBound <- minimum
              
              if (k > 1) {
                segmentLowerBound <- minimum + (((maximum - minimum) * (k - 1)) / linearSegments[i])
              }
              
              lhs <- array(0, dim = nrOutputVars)
              lhs[index] <- -1
              lhs[firstCharacteristicPointIndex + k - 1] <- ((x - segmentLowerBound) / (segmentUpperBound - segmentLowerBound))
              
              if (k > 1) {
                lhs[firstCharacteristicPointIndex + k - 2] <- ((segmentLowerBound - x) / (segmentUpperBound - segmentLowerBound)) + 1
              }
              
              resLhs <- rbind(resLhs, lhs)
              resDir <- c(resDir, "==")
              resRhs <- c(resRhs, 0)
              
              break
            }
          }
        }
      }
      else {
        for (j in seq_len(length(levels[[i]]) - 1)) {
          index <- offsets[i] + j - 1
          
          x <- getEvaluation(perf, altVars, i, index)
          
          for (k in seq_len(linearSegments[i])) {
            segmentUpperBound <- minimum + (((maximum - minimum) * k) / linearSegments[i])
            
            if (x > segmentUpperBound && k == linearSegments[i]) {
              segmentUpperBound <- maximum
            }
            
            if (x <= segmentUpperBound) {
              segmentLowerBound <- minimum
              
              if (k > 1) {
                segmentLowerBound <- minimum + (((maximum - minimum) * (k - 1)) / linearSegments[i])
              }
              
              lhs <- array(0, dim = nrOutputVars)
              lhs[index] <- -1
              lhs[firstCharacteristicPointIndex + k - 1] <- ((segmentUpperBound - x) / (segmentUpperBound - segmentLowerBound))
              
              if (k < linearSegments[i]) {
                lhs[firstCharacteristicPointIndex + k] <- ((x - segmentUpperBound) / (segmentUpperBound - segmentLowerBound)) + 1
              }
              
              resLhs <- rbind(resLhs, lhs)
              resDir <- c(resDir, "==")
              resRhs <- c(resRhs, 0)
              
              break
            }
          }
        }
      }
      
      firstCharacteristicPointIndex <- firstCharacteristicPointIndex + linearSegments[i]
    }
  }
  
  return (list(lhs = resLhs, dir = resDir, rhs = resRhs))
}

###### THRESHOLDS

buildFirstThresholdGraterThen0Constraint <- function(nrVars, firstThresholdIndex, epsilonIndex) {
  lhs <- rep(0, nrVars)
  lhs[firstThresholdIndex] <- 1
  lhs[epsilonIndex] <- -1
  
  return (list(lhs = lhs, dir = ">=", rhs = 0))
}

buildLastThresholdLessThen1Constraint <- function(nrVars, firstThresholdIndex,
                                                  lastThresholdIndex, epsilonIndex) {
  lhs <- rep(0, nrVars)
  lhs[lastThresholdIndex] <- 1
  lhs[epsilonIndex] <- 1
  
  return (list(lhs = lhs, dir = "<=", rhs = 1))
}

buildMonotonousThresholdsConstraints <- function(nrVars, firstThresholdIndex,
                                                 lastThresholdIndex, epsilonIndex) {
  res <- c()
  
  for (i in seq_len(lastThresholdIndex - firstThresholdIndex)) {
    h <- firstThresholdIndex + i
    lhs <- rep(0, nrVars)
    lhs[h] <- 1
    lhs[h - 1] <- -1
    lhs[epsilonIndex] <- -1
    res <- rbind(res, lhs)
  }
  
  if (is.null(res))
    return (NULL)
  else
    return (list(lhs = res, dir = rep(">=", nrow(res)), rhs = rep(0, nrow(res))))
}

###### ASSIGNEMNT EXAMPLES

buildLBAssignmentsConstraint <- function(alternative, atLeastClass, altVars,
                                         firstThresholdIndex, lastThresholdIndex) {
  if (atLeastClass <= 1 || atLeastClass > lastThresholdIndex - firstThresholdIndex + 2)
    return (NULL)
  
  lhs <- altVars[alternative, ]
  lhs[firstThresholdIndex + atLeastClass - 2] <- -1
  
  return (list(lhs = lhs, dir = ">=", rhs = 0))
}

buildUBAssignmentsConstraint <- function(alternative,
                                         atMostClass,
                                         altVars,
                                         firstThresholdIndex,
                                         lastThresholdIndex,
                                         epsilonIndex) {
  if (atMostClass < 1 || atMostClass >= lastThresholdIndex - firstThresholdIndex + 2)
    return (NULL)
  
  lhs <- altVars[alternative, ]
  lhs[epsilonIndex] <- 1
  lhs[firstThresholdIndex + atMostClass - 1] <- -1
  
  return (list(lhs = lhs, dir = "<=", rhs = 0))
}

###### PAIRWISE COMPARISIONS

buildassignmentPairwiseAtLeastComparisonsConstraints <- function(alternativeA,
                                                                 alternativeB,
                                                                 k,
                                                                 altVars,
                                                                 firstThresholdIndex,
                                                                 lastThresholdIndex,
                                                                 firstBinaryVarIndex,
                                                                 epsilonIndex) {
  lhsData <- c()
  dirData <- c()
  rhsData <- c()
  
  sumLhs <- rep(0, ncol(altVars))
  
  for (i in 0:(lastThresholdIndex - firstThresholdIndex - k + 1)) {
    ta <- firstThresholdIndex + i + k - 1
    tb <- firstThresholdIndex + i
    if (ta >= firstThresholdIndex) {
      lhs <- altVars[alternativeA, ]
      lhs[ta] <- -1
      lhs[firstBinaryVarIndex + i] <- RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, ">=")
      rhsData <- c(rhsData, 0)
    }
    
    if (tb <= lastThresholdIndex) {
      lhs <- altVars[alternativeB, ]
      lhs[epsilonIndex] <- 1
      lhs[tb] <- -1
      lhs[firstBinaryVarIndex + i] <- -RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, "<=")
      rhsData <- c(rhsData, 0)
    }
    
    sumLhs[firstBinaryVarIndex + i] <- 1
  }
  
  lhsData <- rbind(lhsData, sumLhs)
  dirData <- c(dirData, "<=")
  rhsData <- c(rhsData, lastThresholdIndex - firstThresholdIndex - k + 1)
  
  return (list(lhs = lhsData, dir = dirData, rhs = rhsData))
}

buildassignmentPairwiseAtMostComparisonsConstraints <- function(alternativeA,
                                                                alternativeB,
                                                                l,
                                                                altVars,
                                                                firstThresholdIndex,
                                                                lastThresholdIndex,
                                                                firstBinaryVarIndex,
                                                                epsilonIndex) {
  lhsData <- c()
  dirData <- c()
  rhsData <- c()
  
  sumLhs <- rep(0, ncol(altVars))
  
  for (i in 0:(lastThresholdIndex - firstThresholdIndex - l + 1)) {
    ta <- firstThresholdIndex + i + l
    tb <- firstThresholdIndex + i - 1
    if (ta <= lastThresholdIndex) {
      lhs <- altVars[alternativeA, ]
      lhs[epsilonIndex] <- 1
      lhs[ta] <- -1
      lhs[firstBinaryVarIndex + i] <- -RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, "<=")
      rhsData <- c(rhsData, 0)
    }
    
    if (tb >= firstThresholdIndex) {
      lhs <- altVars[alternativeB, ]
      lhs[tb] <- -1
      lhs[firstBinaryVarIndex + i] <- RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, ">=")
      rhsData <- c(rhsData, 0)
    }
    
    sumLhs[firstBinaryVarIndex + i] <- 1
  }
  
  lhsData <- rbind(lhsData, sumLhs)
  dirData <- c(dirData, "<=")
  rhsData <- c(rhsData, lastThresholdIndex - firstThresholdIndex - l + 1)
  
  return (list(lhs = lhsData, dir = dirData, rhs = rhsData))
}

###### DESIRED CLASS CARDINALITIES

buildClassCardinalitiesHelperConstraints <- function(alternative,
                                                     altVars,
                                                     firstThresholdIndex,
                                                     lastThresholdIndex,
                                                     firstBinaryVarForThisAlternativeIndex,
                                                     epsilonIndex) {  
  lhsData <- c()
  dirData <- c()
  rhsData <- c()
  
  sumLhs <- rep(0, ncol(altVars))
  
  for (i in 0:(lastThresholdIndex - firstThresholdIndex + 1)) {
    th_1 <- firstThresholdIndex + i - 1
    th <- firstThresholdIndex + i
    
    if (th_1 >= firstThresholdIndex) {
      lhs <- altVars[alternative, ]
      lhs[th_1] <- -1
      lhs[firstBinaryVarForThisAlternativeIndex + i] <- -RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, ">=")
      rhsData <- c(rhsData,-RORUTADIS_BIGM)
    }
    
    if (th <= lastThresholdIndex) {
      lhs <- altVars[alternative, ]
      lhs[th] <- -1
      lhs[epsilonIndex] <- 1
      lhs[firstBinaryVarForThisAlternativeIndex + i] <- RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, "<=")
      rhsData <- c(rhsData, RORUTADIS_BIGM)
    }
    
    sumLhs[firstBinaryVarForThisAlternativeIndex + i] <- 1
  }
  
  lhsData <- rbind(lhsData, sumLhs)
  dirData <- c(dirData, "==")
  rhsData <- c(rhsData, 1)
  
  return (list(lhs = lhsData, dir = dirData, rhs = rhsData))
}

buildClassCardinalitieLBConstraint <- function(class,
                                               min,
                                               nrAlternatives,
                                               nrClasses,
                                               firstIndex) {
  lhs <- rep(0, firstIndex + nrAlternatives * nrClasses - 1)
  for (i in seq(firstIndex + class - 1,
                firstIndex + nrAlternatives * nrClasses - 1, by = nrClasses)) {
    lhs[i] <- 1
  }
  
  return (list(lhs = lhs, dir = ">=", rhs = min))
}

buildClassCardinalitieUBConstraint <- function(class,
                                               max,
                                               nrAlternatives,
                                               nrClasses,
                                               firstIndex) {
  lhs <- rep(0, firstIndex + nrAlternatives * nrClasses - 1)
  
  for (i in seq(firstIndex + class - 1,
                firstIndex + nrAlternatives * nrClasses - 1, by = nrClasses)) {
    lhs[i] <- 1
  }
  
  return (list(lhs = lhs, dir = "<=", rhs = max))
}
###### ADDING CONSTRAINT TO MODEL FOR IMPROVEMENT AND DETERIORATION ASSIGNMENT

addAlternativeThresholdComparisionConstraint <- function(alternative,
                                                         threshold,
                                                         model,
                                                         altVars,
                                                         necessary,
                                                         firstThresholdIndex,
                                                         lastThresholdIndex,
                                                         uxIndex = NULL) {
  if (threshold < 1 || threshold > lastThresholdIndex - firstThresholdIndex + 1)
    return (model)
  
  lhs <- altVars[alternative, ]  
  lhs <- c(lhs, rep(0, ncol(model$lhs) - ncol(altVars)))
  lhs[firstThresholdIndex + threshold - 1] <- -1
  
  dir <- NULL
  if (necessary) dir <- "<="
  else dir <- ">="
  
  if (!is.null(uxIndex)) {
    lhs[uxIndex] <- 1
    lhs[uxIndex + 1] <- -1
  }
  
  return (combineConstraints(model, list(lhs = lhs, dir = dir, rhs = 0)))
}

###### REPRESENTATIVE FUNCTION - CONSTRAINTS

buildUtilityDifferenceConstraint <- function(alternativeA, alternativeB,
                                             altVars, nrVariables) {
  result <- altVars[alternativeA, ]
  
  for (k in 1:length(altVars[alternativeB, ]))
    result[k] <- result[k] - altVars[alternativeB, k]
  
  return (c(result, rep(0, nrVariables - ncol(altVars))))
}

buildUtilityMultipleDifferenceConstraint <- function(alternativeA, alternativeB,
                                                     alternativeC, alternativeD,
                                                     altVars, nrVariables) {
  result <- altVars[alternativeA, ]
  
  for (k in 1:length(altVars[alternativeB, ])) {
    result[k] <- result[k] - altVars[alternativeB, k] +
      altVars[alternativeC, k] - altVars[alternativeD, k]
  }
  
  return (c(result, rep(0, nrVariables - ncol(altVars))))
}

###### CONSTRAINTS HELPERS

combineConstraints <- function(...) {
  allConst <- list(...)
  
  lhs <- c()
  dir <- c()
  rhs <- c()
  types <- c()
  
  for (const in allConst) {
    if (!is.null(const)) {      
      lhs <- rbind(lhs, const$lhs)
      dir <- c(dir, const$dir)
      rhs <- c(rhs, const$rhs)
      types <- c(types, const$types)
    }
  }
  
  return (list(lhs = lhs, dir = dir, rhs = rhs, types = types))
}

removeConstraints <- function(allConst, constraintsToRemoveIndices) {
  return (list(lhs = allConst$lhs[-c(constraintsToRemoveIndices), ],
               dir = allConst$dir[-c(constraintsToRemoveIndices)],
               rhs = allConst$rhs[-c(constraintsToRemoveIndices)],
               types = allConst$types))
}

#### BUILDING MODEL

buildBaseModel <- function(problem,
                           isEpsilonStrictyPositive = FALSE,
                           instedOfModelReturnIndices = FALSE) {
  altVars <- buildAltVariableMatrix(problem$perf)
  epsilonIndex <- ncol(altVars)
  nrAlternatives <- nrow(problem$perf)
  
  firstLevelZeroConstraints <- buildFirstLevelZeroConstraints(problem$perf, problem$criteria)
  bestLevelToUnityConstraint <- buildBestLevelsAddToUnityConstraint(problem$perf, problem$criteria)
  epsilonStrictlyPositive <- NULL
  
  if (isEpsilonStrictyPositive)
    epsilonStrictlyPositive <- buildEpsilonStrictlyPositiveConstraint(ncol(altVars), epsilonIndex)
  
  allConst <- combineConstraints(firstLevelZeroConstraints,
                                 bestLevelToUnityConstraint,
                                 epsilonStrictlyPositive)
  
  monotonousAndCharPointsConstraints <- buildMonotonousAndCharacteristicPointsConstraints(problem$perf,
                                                                                          problem$criteria,
                                                                                          problem$characteristicPoints,
                                                                                          problem$strictVF)
  
  variablesNumberDiff <- ncol(monotonousAndCharPointsConstraints$lhs) - ncol(allConst$lhs)
  if (variablesNumberDiff > 0) {
    for (i in 1:variablesNumberDiff) {
      allConst$lhs <- cbind(allConst$lhs, 0)
      altVars <- cbind(altVars, 0)
    }
  }
  
  allConst <- combineConstraints(monotonousAndCharPointsConstraints, allConst)
  
  firstThresholdIndex <- ncol(altVars) + 1
  
  for (i in 1:(problem$nrClasses - 1)) {
    allConst$lhs <- cbind(allConst$lhs, 0)
    altVars <- cbind(altVars, 0)
  }
  
  actualNrVars <- ncol(altVars)
  lastThresholdIndex <- actualNrVars
  
  firstThresholdGT0Constraint <- buildFirstThresholdGraterThen0Constraint(actualNrVars,
                                                                          firstThresholdIndex,
                                                                          epsilonIndex)
  monotonousThresholdsConstraint <- buildMonotonousThresholdsConstraints(actualNrVars,
                                                                         firstThresholdIndex,
                                                                         lastThresholdIndex,
                                                                         epsilonIndex)
  lastThresholdLT1Constraint <- buildLastThresholdLessThen1Constraint(actualNrVars,
                                                                      firstThresholdIndex,
                                                                      lastThresholdIndex,
                                                                      epsilonIndex)
  
  allConst <- combineConstraints(allConst,
                                 firstThresholdGT0Constraint,
                                 monotonousThresholdsConstraint,
                                 lastThresholdLT1Constraint)
  
  allConst$types <- rep("C", ncol(allConst$lhs))
  
  resrtictionsIndices <- c()
  
  # Constraints: assignemnts
  
  if (is.matrix(problem$assignmentsLB)) {
    for (i in seq_len(nrow(problem$assignmentsLB))) {
      assignmentConst <- buildLBAssignmentsConstraint(problem$assignmentsLB[i, 1],
                                                      problem$assignmentsLB[i, 2],
                                                      altVars,
                                                      firstThresholdIndex,
                                                      lastThresholdIndex)
      allConst <- combineConstraints(allConst, assignmentConst)
      resrtictionsIndices <- c(resrtictionsIndices, nrow(allConst$lhs), nrow(allConst$lhs))
    }
  }
  
  if (is.matrix(problem$assignmentsUB)) {
    for (i in seq_len(nrow(problem$assignmentsUB))) {
      assignmentConst <- buildUBAssignmentsConstraint(problem$assignmentsUB[i, 1],
                                                      problem$assignmentsUB[i, 2],
                                                      altVars,
                                                      firstThresholdIndex,
                                                      lastThresholdIndex,
                                                      epsilonIndex)
      allConst <- combineConstraints(allConst, assignmentConst)
      resrtictionsIndices <- c(resrtictionsIndices, nrow(allConst$lhs), nrow(allConst$lhs))
    }
  }
  
  # Constraints: pairwise comparisions
  
  if (is.matrix(problem$assignmentPairwiseAtLeastComparisons)) {
    for (i in seq_len(nrow(problem$assignmentPairwiseAtLeastComparisons))) {
      firstBinaryVarIndex <- ncol(allConst$lhs) + 1
      for (x in 1:(problem$nrClasses - problem$assignmentPairwiseAtLeastComparisons[i, 3])) {
        allConst$lhs <- cbind(allConst$lhs, 0)
        altVars <- cbind(altVars, 0)
        allConst$types <- c(allConst$types, "B")
      }
      
      resrtictionsIndices <- c(resrtictionsIndices, nrow(allConst$lhs) + 1)
      assignmentConst <- buildassignmentPairwiseAtLeastComparisonsConstraints(problem$assignmentPairwiseAtLeastComparisons[i, 1],
                                                                              problem$assignmentPairwiseAtLeastComparisons[i, 2],
                                                                              problem$assignmentPairwiseAtLeastComparisons[i, 3],
                                                                              altVars,
                                                                              firstThresholdIndex,
                                                                              lastThresholdIndex,
                                                                              firstBinaryVarIndex,
                                                                              epsilonIndex)
      
      allConst <- combineConstraints(allConst, assignmentConst)
      resrtictionsIndices <- c(resrtictionsIndices, nrow(allConst$lhs))
    }
  }
  
  if (is.matrix(problem$assignmentPairwiseAtMostComparisons)) {
    for (i in seq_len(nrow(problem$assignmentPairwiseAtMostComparisons))) {
      firstBinaryVarIndex <- ncol(allConst$lhs) + 1
      for (x in 1:(problem$nrClasses - problem$assignmentPairwiseAtMostComparisons[i, 3])) {
        allConst$lhs <- cbind(allConst$lhs, 0)
        altVars <- cbind(altVars, 0)
        allConst$types <- c(allConst$types, "B")
      }
      
      resrtictionsIndices <- c(resrtictionsIndices, nrow(allConst$lhs) + 1)
      assignmentConst <- buildassignmentPairwiseAtMostComparisonsConstraints(problem$assignmentPairwiseAtMostComparisons[i, 1],
                                                                             problem$assignmentPairwiseAtMostComparisons[i, 2],
                                                                             problem$assignmentPairwiseAtMostComparisons[i, 3],
                                                                             altVars,
                                                                             firstThresholdIndex,
                                                                             lastThresholdIndex,
                                                                             firstBinaryVarIndex,
                                                                             epsilonIndex)
      
      allConst <- combineConstraints(allConst, assignmentConst)
      resrtictionsIndices <- c(resrtictionsIndices, nrow(allConst$lhs))
    }
  }
  
  # Constraints: class cardinalities
  
  firstIndex <- ncol(allConst$lhs) + 1
  
  for (alternative in 1:nrAlternatives) {
    firstBinaryVarIndex <- ncol(allConst$lhs) + 1
    
    for (x in 1:problem$nrClasses) {
      allConst$lhs <- cbind(allConst$lhs, 0)
      altVars <- cbind(altVars, 0)
      allConst$types <- c(allConst$types, "B")
    }
    
    assignmentConst <- buildClassCardinalitiesHelperConstraints(alternative,
                                                                altVars,
                                                                firstThresholdIndex,
                                                                lastThresholdIndex,
                                                                firstBinaryVarIndex,
                                                                epsilonIndex)
    
    allConst <- combineConstraints(allConst, assignmentConst)
  }
  
  
  if (is.matrix(problem$minimalClassCardinalities)) {
    for (i in seq_len(nrow(problem$minimalClassCardinalities))) {
      assignmentConst <- buildClassCardinalitieLBConstraint(problem$minimalClassCardinalities[i, 1],
                                                            problem$minimalClassCardinalities[i, 2],
                                                            nrAlternatives,
                                                            problem$nrClasses,
                                                            firstIndex)
      
      allConst <- combineConstraints(allConst, assignmentConst)
      resrtictionsIndices <- c(resrtictionsIndices, nrow(allConst$lhs), nrow(allConst$lhs))
    }
  }
  
  if (is.matrix(problem$maximalClassCardinalities)) {
    for (i in seq_len(nrow(problem$maximalClassCardinalities))) {
      assignmentConst <- buildClassCardinalitieUBConstraint(problem$maximalClassCardinalities[i, 1],
                                                            problem$maximalClassCardinalities[i, 2],
                                                            nrAlternatives,
                                                            problem$nrClasses,
                                                            firstIndex)
      
      allConst <- combineConstraints(allConst, assignmentConst)
      resrtictionsIndices <- c(resrtictionsIndices, nrow(allConst$lhs), nrow(allConst$lhs))
    }
  }
  
  if (instedOfModelReturnIndices)
    return (resrtictionsIndices)
  else
    return (allConst)
}

#### EXPLANATIONS HELPERS

#' Remove constraints indices by restriction indices
#' 
#' This function allows to remove constraints indices from indices interval by restriction
#' indices.
#' @param constraintIntervalIndices Vector of interval indices of each restriction
#' constraints. c(a_1, b_1, ..., a_n, b_n), where i-th of n restrictions is represented as
#' model constraints at indices between a_i and b_i including a_i, b_i.
#' @param restrictionToRemoveIndices Vector of indices of restrictions to remove.
#' @return Vector of model constraints of restrictions which are NOT in restrictionToRemoveIndices.
removeConstraintsByRestrictions <- function(constraintIntervalIndices, restrictionToRemoveIndices) {
  res <- c()
  nrRestrictions <- length(constraintIntervalIndices) / 2
  
  for (i in 1:nrRestrictions) {
    if (!(i %in% restrictionToRemoveIndices)) {
      res <- c(res, seq(constraintIntervalIndices[2 * i - 1], constraintIntervalIndices[2 * i]))
    }
  }
  
  return (res)
}

