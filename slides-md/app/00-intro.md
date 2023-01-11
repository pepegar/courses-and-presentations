---
title: Advanced Programming with Python
subtitle: Session 1
author: Pepe García <jgarciah@faculty.ie.edu>
email: jgarciah@faculty.ie.edu
---

# Advanced Programming with Python. Session 1

# Professor

Pepe García

<jgarciah@faculty.ie.edu>

Ask me anything

# About the course

>- 15 sessions
>- 1 workgroup assignment
>- Individual work (I'll be grading an individual project from you.  It can be
>  the term integration project, or something else.)

# Syllabus

# SESSION 1

Course presentation. in this session we will introduce the course, the
syllabus, materials we're going to use, and grading system.  Backend development in
Python. We will understand what are the latest tools of Backend development in
Python, from libraries for creating web servers, to others helping with the
creation of development environments such as pipenv.

# SESSION 2, 3

## HTTP in Python

We will use this session to understand the basics of web servers in Python
using Flask, and how to create HTTP clients with Python. We will learn the
following subjects:

>- HTTP Request-Response cycle
>- HTTP Status codes
>- Flask routing
>- Rendering JSON

# SESSION 4, 5 & 6

## HTML Templating

How do we use HTML templates with Flask.

# SESSION 7

## Web servers - Authentication

In this session we will learn about how to implement authentication in web
applications.

# SESSION 8

## Connecting to databases

In this session we will learn how to make our Python applications connect to
databases.  The professor will create a video for the students to follow.

# SESSION 9

## Connecting to databases

In this session we will review what we did in the last async session about
databases, and learn a bit more about how render data from the database to
HTML.

# SESSION 10

## Case: building a Twitter clone in Python

We will use this session to do some hands-on work.  We will tackle a small
project in class in which we will create a Twitter clone with Python.

# SESSION 11

## Group assignment

In this session students will do a group assignment.  We will have time in
class for working on it and ask questions.

# SESSION 12

## Building RESTful APIs in Python

APIs are a way for services online to provide an programatic interface so that
they can be connected to different programs.  In this session we'll learn what
do we mean by RESTful and how to adapt our servers to interact in a RESTful
fashion.

# SESSION 13

## Analytical web applications - Dash

In this session we will introduce a new framework for data oriented web
applications, Dash.  With Dash we will be able to construct data rich
applications in an easy way.

# SESSION 14

## Deployment

In this session we will learn how to deploy our flask applications to the
cloud.

# SESSION 15

## QA session

In this session we will do a whirlwind tour over what we have learned in the
course and we will have time to answer questions students may have

# Grading criteria

|Criteria                            |Score                              |
|:-----------------------------------|----------------------------------:|
|Class participation                 |**10%**                            |
|Workgroups                          |**30%**                            |
|Individual work                     |**60%**                            |

# Intro

\begin{exampleblock}{What are we really going to learn in this course?}
Let's draw!
\end{exampleblock}

# HTTP

\begin{exampleblock}{What happens when you type an address in your browser?}
\end{exampleblock}

# HTTP

. . .

HTTP is a request-response protocol.  HTTP **clients send requests** and
HTTP **servers answer with responses**.

# HTTP.  URLs

Uniform Resource Locators.

![](https://i.insider.com/601c27acee136f00183aa4f5?width=750&format=jpeg&auto=webp)

# HTTP

Depending on the intention of the request, HTTP describes different
methods:

. . .

  method       **intention**
  ------------ ----------------------
  **GET**      read to a resource
  **POST**     update a resource
  **PUT**      create a resource
  **DELETE**   delete a resource

# Repo for today

https://github.com/mcsbt-app-2022/session-1
