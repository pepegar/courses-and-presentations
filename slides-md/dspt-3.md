---
title: Data Structures & Programmatic Thinking
subtitle: Session 3
author: Pepe García <jgarciah@faculty.ie.edu>
email: jgarciah@faculty.ie.edu
---

## Plan for this session

. . .

- Python basic datatypes

. . .

- Variables

. . .

- Operators

. . .

- Basic functions

# Datatypes

Datatypes tell Python how we want to use the data.  There are several
primitive data types in Python such as **bool**, **int**, **str**,
**float**.

# Datatypes

## Integers

Integers (or ints) represent whole numbers.  We create them by using
their numeric representation directly.

```python
1
234
432432
```

. . .

\begin{exampleblock}{Demo}
\end{exampleblock}

---

# Datatypes

## Floating point numbers

Floats represent numbers that have a fractional part.  We use a dot to
separate the integer and fractional parts:

```python
3.14
1.0
33.33
```

. . .

\begin{exampleblock}{Demo}
\end{exampleblock}

---

# Datatypes

## Strings

Strings are used for textual representation. They can be created using
either double or simple quotes.

```python
'this is a string'
"this is another string"
```

. . .

\begin{exampleblock}{Demo}
Why can one use either double or single quotes? why just not agree on one of them?
\end{exampleblock}

---

# Datatypes

## Booleans

Booleans represent truthiness. There are only two values in for the bool
type in Python: True and False

```python
True
False
```

. . .

\begin{exampleblock}{Demo}
\end{exampleblock}

---

# Getting the type of a value

We can always get the type of a value using the **type(value)**
function

```python
type("patata")
```

---

# Getting the type of a value

\begin{exampleblock}{Practice}

Inside Spyder, check what's the type of the following expressions:

\begin{itemize}
\item \textbf{\texttt{"there is some text here"}}
\item \textbf{\texttt{1}}
\item \textbf{\texttt{True}}
\item \textbf{\texttt{44.4}}
\item \textbf{\texttt{'true'}}
\item \textbf{\texttt{'False'}}
\item \textbf{\texttt{2}}
\item \textbf{\texttt{'33.3'}}
\end{itemize}

\end{exampleblock}

---

# Operators

Operators are symbols in the language that perform different kinds of
computations on values

They're **binary**, they will operate on two values.

# Arithmetic Operators

| symbol   | meaning          |
| :------- | :--------------- |
| **`+`**  | sum              |
| **`-`**  | substraction     |
| **`*`**  | multiplication   |
| **`/`**  | division         |
| **`**`** | exponentiation   |
| **`//`** | floored division |
| **`%`**  | modulus          |

# Arithmetic Operators

## Rules of precedence

>- Parentheses
>- Exponentiation
>- Multiplication/Division
>- Sum/Substraction
>- when operators have the same precedence, evaluate left to right

. . .

\begin{exampleblock}{Demo}
\end{exampleblock}

# String operators

Sum and multiplication operators work on strings too.  They're used to
concatenate and multiply strings, respectively.

. . .

\begin{exampleblock}{Demo}
\end{exampleblock}


# Variables

Variables are names that point to values in Python.  We declare them
using the assignment operator (**`=`**).

```python
variable_name = "value"
```

# Variables

\begin{block}{Naming variables}
It's important to be as descriptive as possible when naming variables

There are some naming rules we should obey
\end{block}

. . .

\begin{alertblock}{Rules}
\begin{itemize}
\item variable names can't start with a number
\item variable names can't contain special characters such as \textbf{!}, \textbf{@}, \textbf{.}
\item Can't be one of the reserved words
\end{itemize}
\end{alertblock}

# Variables

## Reserved words

|            |           |          |            |         |
| ---------- | --------- | -------- | ---------- | ------- |
| `and`      | `del`     | `from`   | `None`     | `True`  |
| `as`       | `elif`    | `global` | `nonlocal` | `try`   |
| `assert`   | `else`    | `if`     | `not`      | `while` |
| `break`    | `except`  | `import` | `or`       | `with`  |
| `class`    | `False`   | `in`     | `pass`     | `yield` |
| `continue` | `finally` | `is`     | `raise`    |         |
| `def`      | `for`     | `lambda` | `return`   |         |

# Variables

## Mutability

In Python variables are mutable. This means that we can change their
value at any time

```python
name = "Pepe"
print(name)

name = "Jose"
print(name)
```

# Converting values

There are some times when we need to convert a value from one type to
another.

We use the **int()**, **bool()**, **str()**, and **float()** functions for that

. . .

```python
int('23')
bool(1)
bool(0)
str(True)
float("3.2")
```

# Printing output

One can print output using the **print()** function

# User input

There is a handy function **input()** that allows us to capture input
from the user

```python
name = input("Tell me your name: ")

print("hello, " + name)
```

# Recap

>- Datatypes (int, float, bool, str)
>- Variables (naming, mutability)
>- Operators (arithmetic, precedence, string operators)
>- Converting values
>- User input

# Exercises

1. Create a program that calculates the total number of seconds in an hour
2. How does the following expression evaluate?

   2 + (3 + 4) + (5 * 33 ** 34)

3. Create a program that asks the user for their age and their mother's 
   age and calculate the age difference

4. What are the results and result types of the following expressions?
   think it yourself, do not use the Python console for this

   3 * 5 * 2
   3 / 11
   3 // 11
   25 % 2

5. Make the following expressions work (use Python console for this one)
   3 + "3"
   'there are ' + 4 ' dogs barking'