---
title: Programming fundamentals with Python
author: Pepe García
email: jgarciah@faculty.ie.edu
date: 2020-04-20
lang: en
---

Programming fundamentals with Python
====================================


Plan for today
==============

The Internet

HTTP

JSON

requests library

Web APIs

The Internet
============


0:46 - 1:35

The Internet
============

The internet is a VERY BIG computer network.  It\'s like a **graph** of
computers ones connected to anothers.

HTTP
====

HTTP is the protocol that moves The Internet:

Based on **requests** and **responses**

**Clients** do requests and **servers** answer with responses

HTTP Requests
=============

HTTP requests and responses are messages interchanged between client and
server

HTTP requests may contain a lot of metadata but for us, today, the only
field that matters is the URL:

HTTP Clients
============


Web browsers are basically HTTP clients that allow us to navigate the
web with our computer

HTTP Clients
============

Deconstruct what happens when we browse the web (Developer mode)

 

start at

[[https://en.wikipedia.org/wiki/Echidna]{style="color:#ADD8E6"}](https://en.wikipedia.org/wiki/Echidna)

 

Web APIs
========

Web APIs, or just APIs are the most common way for exposing information
from a web server


JSON
====

<http://json.org>

JSON is a data interchange format used to share data between HTTP
clients and servers.  Some valid JSON values are:

    [1,2,3] # lists

    1 # numbers

    "potatoes" # Strings

    {"name":"Pepe","surname":"Garcia"} # dictionaries

JSON
====

<http://json.org>

JSON is very similar to how we declare our data in Python but the cool
thing about it is that it can be used **from any language**.

 

For example, a **web API** can be written in Java, and we use it from
Python because both **client and server understand JSON**

JSON
====

Explain JSON

requests library
================

Requests is the most famous HTTP library for Python.  It has an HTTP
client as well as other useful utilities such as JSON handler, etc.

requests library
================

We can use requests to get an HTTP response as follows:

``` {.nimrod}
import requests

response = requests.get("url")

data = response.json()
```

requests library
================

Example of how **requests** works.

 

How do we obtain the JSON from the response?

 

Use
[[**http://api.open-notify.org/astros.json**]{style="color:#ADD8E6"}](http://api.open-notify.org/astros.json)
as an example

requests library
================

Use the Star Wars API to list all planet names from star wars.

 

**https://swapi.co/**

requests library
================

Use Github\'s API to list all repositories in your github account:

 

**https://developer.github.com/v3/repos/\#list-user-repositories**

Fuel for crazy ideas
====================

<https://github.com/toddmotto/public-apis>

Exercises
=========

Exercise 1
==========

Create a function that uses the **requests** library to get the lyrics
of a song.

 

You can use the **lyrics.ovh** api as described here:
https://lyricsovh.docs.apiary.io/\#reference/0/lyrics-of-a-song/search?console=1

Exercise 1
==========

Create a function that returns the current latitude and longitude of the
ISS

 

http://api.open-notify.org/

Exercise 3
==========

using the given population API, create a program that:

 

\- gets a list of all available countries

\- Gets the first 10 countries

\- Gets the country\'s today & tomorrow population.

 

http://api.population.io/\#!/countries/listCountries
