---
title: Programming fundamentals with Python
subtitle: Command Line Interface
author: Pepe García <jgarciah@faculty.ie.edu>
email: jgarciah@faculty.ie.edu
---


# Plan for today

>- Learn a bit about CLI tools
>- Learn about version control systems

# Installing Git

If you don't have it installed, you can get it from
**https://git-scm.com/downloads**

# Command line

The command line allows users to navigate the computer and manage it.  We can do
almost the same things with the command line and a graphical user interface.

![](./img/command-line.jpg)


# Command line

## Disclaimer

In this slide set, every time you see a **`$`** at the beginning of
the line it means that that's a command to be written in the terminal.

. . .

## Disclaimer 2

If you're on Mac, we will use the **Terminal** for today's session, if
you're on Windows, please open **Git Bash**.


# Listing files

We can **list files** in a folder using the **ls** command.

```
$ ls

Desktop   Documents Downloads Library   Movies    Music     Pictures  Public    opt       projects
```

# Changing directories

We change directories (move around) using **cd**.

```
$ ls

Desktop   Documents Downloads Library   Movies    Music     Pictures  Public    opt       projects

$ cd Desktop
```

# Changing directories

We can go to *upper* directories using **cd ..**

```
$ ls

Desktop   Documents Downloads Library   Movies    Music     Pictures  Public    opt       projects

$ cd Desktop

$ cd ..

$ ls

Desktop   Documents Downloads Library   Movies    Music     Pictures  Public    opt       projects
```

# Getting current directory

We can see where we are with the **pwd** command

```
$ pwd
/Users/pepe

$ cd Desktop

$ pwd
/Users/pepe/Desktop
```

##

**pwd** stands for print working directory

# Creating directories

One can create directories using the **`mkdir`** command:


```
$ pwd
/Users/pepe

$ mkdir hello_dolly

$ cd hello_dolly

$ pwd
/Users/pepe/hello_dolly
```
