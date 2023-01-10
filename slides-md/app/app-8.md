---
title: Advanced Programming with Python. Session 8
author: Pepe García
email: jgarciah@faculty.ie.edu
date: 2020-04-20
lang: en
---

Advanced Programming with Python. Session 8
===========================================


Plan for today
==============

-   Learn about virtualenv
-   Learn about Heroku
-   Deploy our first app to Heroku

Virtualenv
==========

So far, everytime we\'ve needed to install a dependency we\'ve done it
globally.

 

In real world python projects we\'ll try to avoid that, and we\'ll use
individual environments per project.

```python
pip3 install virtualenv
```

Virtualenv (conda)
==================

We can only have **one virtualenv active** at a time.  So, the first
thing we\'ll need to do for deactivating anaconda\'s is just to call to
**deactivate**

```python
(base) pepe:session-8 $ deactivate
pepe:session-8 $
```

Virtualenv
==========

**virtualenv** is used to manage dependencies per project.

 

There are two steps for using a virtualenv:

```python
pepe:session-8 $ virtualenv venv # create a virtualenv named venv
pepe:session-8 $ . venv/bin/activate # activate the virtualenv
(venv) pepe:session-8 $ # the virtualenv name will appear in the prompt
```

Virtualenv
==========

It\'s not needed to have the virtualenv directory (in our case **venv**)
checked into git, so we can ignore it:

```python
pepe:session-8 $ echo "venv" > .gitignore
```

Heroku
======

Heroku is a PAAS that we can use to run our applications in the cloud.

 

https://heroku.com

Practice
========

Creating an account in Heroku

Using Heroku
============

We will be able to manage most of our heroku app using the webapp
itself, but it will be handy to install the CLI tool as well

 

[**https://devcenter.heroku.com/articles/heroku-cli**](https://devcenter.heroku.com/articles/heroku-cli)

Practice
========

Setting up a simple heroku app.

 

1.  clone session-8 repo
2.  create a virtualenv for it (**virtualenv venv**)
3.  install flask in the virtualenv
4.  freeze dependencies in a **requirements.txt**)
5.  setup heroku (**heroku create**)
6.  push to heroku (**git push heroku master**)
