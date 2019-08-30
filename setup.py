#!/usr/bin/env python

from setuptools import setup
import sys

if sys.version_info[:2] < (3, 5):
    sys.stderr.write(
        'This version of dpcontracts requires Python 3.5 - either upgrade '
        'to a newer version of pip that handles this automatically, or '
        'explicitly "pip install dpcontracts<0.6".'
    )
    sys.exit(1)

setup()
