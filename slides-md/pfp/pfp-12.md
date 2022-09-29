---
title: Programming fundamentals with Python
subtitle: Sorting algorithms - mergesort
author: Pepe García <jgarciah@faculty.ie.edu>
email: jgarciah@faculty.ie.edu
date: 2020-11-06
lang: en
---

# Plan for today

>- recursion
>- divide and conquer algorithms
>- mergesort

# Recursion

::: columns
:::: column
![](./img/recursive-book.jpeg)
::::
::::column
Recursion is a technique to solve problems in terms of smaller versions of the
same problem.

. . .

In computer science we use it when a function calls itself:

. . .

```python
def factorial(n):
    if n == 0:
        return 1
    else:
        return n * factorial(n - 1)
```

::::
:::

# Recursion

::: columns
:::: column
![](./img/droste.jpg)
::::
::::column

An example of a recursive algorithm is the calculation of a number in the
Fibonacci sequence.

Remember that Fibonacci goes like this:

**0, 1, 1, 2, 3, 5, 8, 13...**

. . .

\begin{exampleblock}{Fibonacci}

Let's implement the calculation of a number in the Fibonacci sequence using recursion!

\end{exampleblock}

::::
:::

# Recursion

Something that we have to consider is that all problems that we solve using
recursion can be solved using iteration.

. . .

\begin{block}{Homework}

Try implementing the previous function using iteration instead of recursion!

\end{block}

# Divide and conquer

::: columns
:::: {.column width=20%}
![](./img/Philip-ii-of-macedon.jpg)
::::
:::: {.column width=80%}

From Wikipedia:

> Divide and rule (Latin: divide et impera), or divide and conquer, in politics
> and sociology is gaining and maintaining power by breaking up larger
> concentrations of power into pieces that individually have less power than the
> one implementing the strategy.

. . .

_Divide and conquer_ is a technique used **in algorithmia** in which we split a
problem into smaller sub-problems recursively until they're simple enough to be
solved directly.

::::
:::

# 

\begin{exampleblock}{Checkpoint}
How is the session going so far?
- Do we have questions?
- Is there anything that doesn't yet click?
\end{exampleblock}

# Mergesort

The idea behind **mergesort** is fairly simple.  What if we had a way of
splitting an unsorted list into smaller ones, and then merging them together in
a sorted fashion?

. . .

A question we need to agree on before jumping into the implementation...

- **Is a list of only one element sorted?**

. . .

Yes, it is!

# Mergesort

![](./img/mergesort.png){height=300px}

# Mergesort

In our mergesort implementation we will have two different functions.
**`merge`**, that will just take two **sorted** lists and merge them into a new
sorted list, and **`mergesort`**, that will perform the splitting of the list
and call **`merge`** on the smaller lists.

. . .

\begin{exampleblock}{Mergesort}
Let's implement mergesort!
\end{exampleblock}

# Mergesort

What's the worst case runtime for mergesort?  Why?