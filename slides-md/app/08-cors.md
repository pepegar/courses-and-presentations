---
title: Advanced Programming with Python
subtitle: CORS
author: Pepe García <jgarciah@faculty.ie.edu>
email: jgarciah@faculty.ie.edu
---

# What's CORS

cors is a security feature that restricts what resources a web page can request
from another domain. It is a security feature implemented in web browsers to
prevent JavaScript from making requests to a different domain than the one that
served the web page.

# How does it work

CORS works by adding new HTTP headers that allow servers to serve resources to
permitted origin domains. Browsers support these headers and respect the
restrictions they establish.

# How to enable CORS

CORS is enabled by default in most web servers. However, you can configure it
to allow or restrict access to your resources.

# CORS in Flask

In Flask, you can enable CORS by using the `flask-cors` package. This package
provides a decorator that you can use to enable CORS in your routes.

```python
from flask import Flask, jsonify
from flask_cors import CORS

app = Flask(__name__)
CORS(app)

@app.route('/hello')
def hello():
    return jsonify({'message': 'Hello, World!'})
```

# What do we mean by resource sharing?

Resource sharing is the process of allowing a web page to request resources from
a different domain. This is a security feature that prevents malicious
JavaScript from making requests to a different domain than the one that served
the web page.

# Why do we need it?

We may be hosting our API in Google Cloud, and our React client locally.  In this case we need to enable CORS in our API to allow the React client to make requests to it.

# How to enable it?

```python
from flask import Flask, jsonify
from flask_cors import CORS

app = Flask(__name__)
CORS(app)

@app.route('/hello')
def hello():
    return jsonify({'message': 'Hello, World!'})
```
