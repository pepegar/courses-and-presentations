---
title: Programming fundamentals with Python
subtitle: session 4
author: Pepe García <jgarciah@faculty.ie.edu>
email: jgarciah@faculty.ie.edu
date: 2020-10-13
lang: en
---

# Plan for this session

>- learn about **git clone**
>- clone the repository we created through Github Classroom
>- apply git operations we know the newly cloned repository

# Async session

In this session we will do an example of what will be a assignment handled
through Github and Github Classroom.


# Cloning a repository

We use **`git clone`** to clone a git remote repository **that doesn't yet
exists in our computer** into a new folder in our computer.

Consider that **`git clone`** will create a new working directory within the
current folder, and put the local repository inside.  I try to have a folder on
my computer with all my repositories, in my case is in **`/Users/pepe/projects`**.

# Cloning a repository

```
$ pwd
/Users/pepe

$ git clone https://github.com/pepegar/my-first-repository.git

Cloning into 'my-first-repository'...
remote: Enumerating objects: 16, done.
remote: Total 16 (delta 0), reused 0 (delta 0), pack-reused 16
Unpacking objects: 100% (16/16), done.
```

This will clone the repository in **`/Users/pepe/my-first-repository`**.

# Cloning a repository

Now that we know how to create a repository, let's do it with the one we
created through Github Classroom.

In case you haven't yet accepted the assignment, accept it from this link:
[https://classroom.github.com/a/csu9qbqV](https://classroom.github.com/a/csu9qbqV).

You'll need to authorize Github and accept the invitation to the **pfp-2020** class.

# Cloning a repository

This will create a new repository in [https://github.com/pfp-2020](https://github.com/pfp-2020), find it and get the **HTTPS** clone url for it:

![](./img/https-url.png)

Now copy it, and **`git clone`** it!

# Exercises to do in our local repository

>- Create a file called exercise.py
>- Create a function inside the file called **is_even** that receives a number as a parameter returns **`True`** if the number is even.
>- Create a function inside the file called **is_odd** that receives a number as a parameter returns **`True`** if the number is odd.

Commit your changes for each of your previous steps.

# Exercises to do in our local repository

After doing the previous exercises, you'll need to **push to the repository**.  Consider that, when cloning a repository, one doesn't need to setup the **`git remote`**, because **`git clone`** does it automatically for us.

# References

The Coding Train has a great tutorial series on Youtube about git.  The lesson that gets into cloning is this one.
https://www.youtube.com/watch?v=yXT1ElMEkW8