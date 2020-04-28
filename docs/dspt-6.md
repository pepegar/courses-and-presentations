---
title: Data Structures & Programmatic Thinking
author: Pepe García
email: jgarciah@faculty.ie.edu
date: 2020-04-20
lang: en
---

Data Structures & Programmatic Thinking
=======================================

https://slides.com/pepegar/dspt-6/live

Plan for today
==============

Mutability

Iteration

Mutability
==========

Mutability is a feature of variables in most programming languages.  It
means that variables can be updated to newer values.

``` {.stylus}
x = 1
x = x * 3

print(x)
```

Mutability
==========

Iteration
=========

Iteration is the act of repeating a process.  In Python we express
iteration with the **while** statement

While
=====

1\. Evaluate the condition

2\. If the condition is False, exit while and go to next statement

3\. If condition is true, execute body.  Then go to step 1.

While
=====

Stopping a loop
===============

You can always stop a loop using the break keyword

```python
while True:
    if im_bored_of_iterating:
        break
    else:
        print("i'm iterating!")
     
```

Infinite loops
==============

Infinite loops are loops whose condition never evaluates to False.  This
means that they\'ll run forever (unless we break them)

``` {.stylus}
+ Create a function that prints the numbers 1 to 50 (using iteration)

+ Create a program that prints multiplication tables from 1 to 10

+ Create a function ~pyramid~ that receives an integer ~n~ as
  parameter and prints ~n~ lines of the following pattern:

  *
  **
  ***
  ****
  *****

+ Create a function ~inverted_piramid~ that writes the pyramid of
  stars in an inverted fashion.

  *****
  ****
  ***
  **
  *

+ Create a function ~multiplicate~ that takes two integers (~a~ and
  ~b~, for example) and returns a times b.  Do not use the ~*~
  operator.

+ Create a function ~exponentiate~ that takes two arguments ~base~
  and ~exponent~ and raises ~base~ to the ~exponent~ power.  Do not
  use the exponentiation operator.
```
