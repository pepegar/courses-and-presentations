---
title: Programming Thinking
subtitle: Hardware
author: Pepe García
email: Pepe García<jgarciah@faculty.ie.edu>
---

# Plan for this session

>- Learn a bit about hardware
>- Try the VSCode editor

# CPU

::: columns

:::: column

![](./img/cpu.jpg)

::::

:::: column

>- It's the part of the computer capable of _computing_.
>- Speed measured in hertz

::::

:::

# CPU

## Moore's law

:::columns
::::column

> Moore's law is the observation that the number of transistors in a
> dense integrated circuit (IC) doubles about every two years. Moore's
> law is an observation and projection of a historical trend. Rather
> than a law of physics, it is an empirical relationship linked to
> gains from experience in production.

::::
::::column

![](./img/moore.png)

::::
:::

# CPU

\begin{alertblock}{Moore's law}

Nowadays, although the number of transistors in chips is still
increasing over the years, the pace has slowed down.  The way we're
achieving faster speeds nowadays is by having more cores working at
the same time.

\end{alertblock}

http://www.gotw.ca/publications/concurrency-ddj.htm

# RAM

Not this _Random Access Memories_...

![](./img/ram_daft_punk.jpg){height=70%}

# RAM

::: columns

:::: column

But **this** Random Access Memory!

::::

:::: column

![](./img/ram.jpg)

::::

:::

# RAM

::: columns

:::: column

>- RAM is the short term memory of a computer
>- Think of it like a big shared blackboard
>- Divided in addresses
>- Not persistent.  _if computer is powered down, contents are lost_
>- Fast (Random Access)

::::

:::: column

![](./img/ram.jpg)

::::

:::

# HDD / SSD

>- Hard Disk Drives or Solid State Drives are the long term storage of the computer
>- Persistent
>- Slower than RAM
>- Higher capacity than RAM


# Recap.  What happens when Spyder runs a file?

\begin{exampleblock}{Whiteboard}
Let's understand what happens in under the hood of our computer when we run a file in VSCode
\end{exampleblock}

# Review

. . .

>- **CPU** is the _computing_ part of our computer
>- **RAM** is used for the runtime of our programs to hold volatile data
>- **HDD / SSD** stores non-volatile data, it's **way** slower than RAM. (http://norvig.com/21-days.html#answers)
