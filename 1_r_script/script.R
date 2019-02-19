## Example on an R script file 

# this is a comment

## Charater strings
x <- "Hello"  # assignment
y <- "world"
x             # print
print(x)
x + y         # error
z <- paste0(x, " ", y)  # use paste0 to concatenate 
z
cat(z)  # a more native way of printing (good inside functions)


## Getting help 
?cat
?class
?str


## Working dir - in general a good idea to set it to the where the script file is
getwd()
setwd("C:/Users/au15463/Dropbox/work_private/admin/LOG/r_workshop/1_r_script")


## Install missing packages
install.packages("tidyverse")


## load a package
library(tidyverse)


## Data types
y <- 1:4
z <- 3.5
p <- pi
class(x)
str(x)
class(y)
class(y[1])
str(y)
str(y[1])
class(z)
str(z)
class(p)
str(p)


## Matrices - all elements must be of same type (e.g. numeric)

# Elements are arranged sequentially by row.
M <- matrix(c(3:14), nrow = 4, byrow = TRUE)
M

# Elements are arranged sequentially by column.
N <- matrix(c(3:14), nrow = 4, byrow = FALSE)
N

# Define the column and row names.
rownames = c("row1", "row2", "row3", "row4")
colnames = c("col1", "col2", "col3")
row.names(N) = rownames
N

P <- matrix(c(3:14), nrow = 4, byrow = TRUE, dimnames = list(rownames, colnames))
P

# Access to elements (guess the output)
P[1,3]
P[4,2]
P[2,]
P[,3]

## Matrix Addition & Subtraction
# Create two 2x3 matrices.
matrix1 <- matrix(c(3, 9, -1, 4, 2, 6), nrow = 2)
matrix1
matrix2 <- matrix(c(5, 2, 0, 9, 3, 4), nrow = 2)
matrix2

# Add the matrices.
result <- matrix1 + matrix2
cat("Result of addition","\n")
result

# Subtract the matrices
result <- matrix1 - matrix2
cat("Result of subtraction","\n")
result



# Create two 2x3 matrices.
matrix1 <- matrix(c(3, 9, -1, 4, 2, 6), nrow = 2)
print(matrix1)

matrix2 <- matrix(c(5, 2, 0, 9, 3, 4), nrow = 2)
print(matrix2)

# Multiply the matrices (elementwise)
matrix1
matrix2
result <- matrix1 * matrix2
cat("Result of multiplication","\n")
result

# Divide the matrices (elementwise)
result <- matrix1 / matrix2
cat("Result of division","\n")
result

# Matrix multiplication
matrix1
matrix2 <- t(matrix2)  # transpose
result <- matrix1 %*% matrix2
cat("Result of division","\n")
result


## Sparse matrices  
library(Matrix)
matrix1 <- Matrix(c(3, 9, -1, 4, 2, 6), nrow = 2)
class(matrix1)
str(matrix1)




## If you want to run all the script then use source
source('script.R')