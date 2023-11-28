---
title: Programming fundamentals for Python
subtitle: HTTP
author: Pepe García <jgarciah@faculty.ie.edu>
email: jgarciah@faculty.ie.edu
date: 2020-04-20
lang: en
---

# Plan for today

>- Internet basics
>- HTTP
>- Requests library
>- Exercises

# The Internet

The internet is a **VERY BIG** computer network.  It forms a **graph** of
computers ones connected to others.

# Internet

\begin{exampleblock}{}
Discuss the Internet in the whiteboard.
\end{exampleblock}

# HTTP

HTTP is the protocol that powers The Internet:

Based on **requests** and **responses**.

**Clients** do requests and **servers** answer with responses

# HTTP requests

```http
GET / HTTP/1.1
Accept: text/html

Host: www.example.com
```

# HTTP Responses

Status

```python
HTTP/1.1 200 OK

Date: Mon, 23 May 2005 22:38:34 GMT
Content-Type: text/html; charset=UTF-8
Content-Length: 138
Last-Modified: Wed, 08 Jan 2003 23:11:55 GMT
Server: Apache/1.3.3.7 (Unix) (Red-Hat/Linux)
ETag: "3f80f-1b6-3e1cb03b"
Accept-Ranges: bytes
Connection: close

{"user": "pepegar", "age": 55}
```

# HTTP Requests

HTTP requests and responses are messages interchanged between client and
server

HTTP requests may contain a lot of metadata but for us, today, the only
field that matters is the URL:

# HTTP Clients

HTTP clients send requests to HTTP servers.  The most iconic case for
HTTP clients is web browsers.

Web browsers are HTTP clients that allow us to navigate the web with our
computer.

# HTTP Clients

Deconstruct what happens when we browse the web (Developer mode)

start at <https://en.wikipedia.org/wiki/Echidna>
 

Web APIs
========

Web APIs, or just APIs are the most common way for exposing information
from a web server.


# Web APIs

Most web APIs communicate using a data interchange format such as
**JSON** or **XML**.

# JSON

<http://json.org>

JSON is a data interchange format used to share data between HTTP
clients and servers.  Some valid JSON values are:

```json
[1,2,3] # lists

1 # numbers

"potatoes" # Strings

{"name":"Pepe","surname":"Garcia"} # dictionaries
```

# Using JSON

```python
json_encoded_string = """
    {"name": "Pepe", "last_name": "García"}
    """
```

Let's **parse** this JSON string from Python using the **json ** module

# requests library

Requests is the most famous HTTP library for Python.  It has an HTTP
client as well as other useful utilities such as JSON handler, etc.

 

It should be already installed in your computers thanks to Anaconda.

# requests library

We can use requests to get an HTTP response as follows:

``` {.python}
import requests

response = requests.get("url")

data = response.text
```

# Practice

Let's try using **requests** to get the homepage of http://google.com

# requests + json

Requests has builtin function for handling JSON responses

```python
response = requests.get('https://swapi.dev/api/starships/9')

response.json()
```

# requests library

Use https://swapi.dev/api/starships/9

Call the API and print the name and model of the spaceship!

# requests library

Use the Github API to retrieve all the public repositories in our
organization!

https://api.github.com/orgs/mcsbt-2023/repos

. . .

Then, for each one of them, print all commit messages.

. . .

https://api.github.com/repos/mcsbt-2023/session-16/commits

`data["commit"]["message"]`

# Fuel for crazy ideas

<https://github.com/toddmotto/public-apis>
