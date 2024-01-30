---
title: Advanced Programming with Python
subtitle: REST APIs
author: Pepe García <jgarciah@faculty.ie.edu>
email: jgarciah@faculty.ie.edu
---

# Plan for today

- REST
- REST in the server with Flask
- consuming REST APIs wiht requests

# What's an API


::: columns

:::: column

## From Wikipedia

> An application programming interface is a way for two or more computer
> programs to communicate with each other. It is a type of software interface,
> offering a service to other pieces of software. A document or standard that
> describes how to build or use such a connection or interface is called an API
> specification. [Wikipedia](https://en.wikipedia.org/wiki/API)

::::

:::: column


::::

:::

# What's an API

Basically, a way of exposing a web server so that it can be used **from other
software components**.

In order to be used from other software components, they must use a data
interchange format.  In our examples we'll use JSON.

# What's REST

We call REST APIs to APIs that follow some particular principles:

- They use **URIs for resources**
- They're **stateless**

# What's REST. URIs for resources

_Resources_ in your API must be represented as URIs.

Different operations on them are represented with different HTTP methods on
that URI.

- `POST` for creating a resource
- `GET` for reading a resource
- `PUT` for updating a resource
- `DELETE` for deleting a resource

## Example URIs

```
http://api.pepe.com/games/1
http://aws.amazon.com/ec2/instances/0f9304a4-e4f8-4d95-acce-bc92794cf365
```

# What's REST. Statelessness

This means that the HTTP Request must come with everything needed in order to
fulfill it.

# Creating REST APIs in Flask

## Example

Let's see an example of a REST API in `api.py`.

# Creating REST APIs in Flask

## Exercise

Create a new endpoint in our API that returns a JSON with all transactions for a
given user.

# Creating REST APIs in Flask

## Exercise

Create a endpoint in our API that allows updating a user's shop.

# Consuming REST APIs with requests

All HTTP methods that we talked about before are represented as function in the
**`requests`** library.

```python
import requests

requests.get("http://localhost:8080/users")
requests.post("http://localhost:8080/users", json={"a": 1})
requests.put("http://localhost:8080/users", json={"a": 1})
requests.delete("http://localhost:8080/users")
```

# Consuming REST APIs with requests

Create an endpoint to delete a users's transaction.
Call the endpoint from client.py

# Alternatives to Flask to build REST APIs

Nowadays it's very common to use [FastAPI](https://fastapi.tiangolo.com/)
instead of Flask for REST APIs.  It's
inspired by Flask, and has lots of interesting functionality, check it out!
