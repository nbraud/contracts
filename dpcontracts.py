#!/usr/bin/env python3

__all__ = ["ensure", "invariant", "require", "transform", "rewrite",
           "preserve", "PreconditionError", "PostconditionError"]
__author__ = "Rob King"
__copyright__ = "Copyright (C) 2015-2018 Rob King"
__license__ = "LGPL"
__version__ = "$Id$"
__email__ = "jking@deadpixi.com"
__status__ = "Alpha"

from ast import parse
from collections import namedtuple
from functools import wraps
from inspect import isfunction, ismethod, iscoroutinefunction, getfullargspec, getsource
from sys import version_info

if version_info[:2] < (3, 5):
    raise ImportError('dpcontracts >= 0.6 requires Python 3.5 or later.')

class PreconditionError(AssertionError):
    """An AssertionError raised due to violation of a precondition."""

class PostconditionError(AssertionError):
    """An AssertionError raised due to violation of a postcondition."""

def get_function_source(func):
    try:
        source = getsource(func)
        tree = parse(source)
        decorators = tree.body[0].decorator_list
        function = tree.body[0]
        first_line = decorators[0].lineno
        following_line = first_line + 1
        if len(decorators) > 1:
            following_line = decorators[1].lineno
        elif len(function.body) > 0:
            following_line = function.body[0].lineno - 1
        return "\n".join(source.split("\n")[first_line - 1:following_line - first_line]) + " failed"

    except (SyntaxError, OSError):
        return str(func)

def get_wrapped_func(func):
    while hasattr(func, '__contract_wrapped_func__'):
        func = func.__contract_wrapped_func__
    return func

def build_call(func, *args, **kwargs):
    """
    Build an argument dictionary suitable for passing via `**` expansion given
    function `f`, positional arguments `args`, and keyword arguments `kwargs`.
    """

    func = get_wrapped_func(func)
    named, vargs, _, defs, kwonly, kwonlydefs, _ = getfullargspec(func)

    nonce = object()
    actual = dict((name, nonce) for name in named)

    defs = defs or ()
    kwonlydefs = kwonlydefs or {}

    actual.update(kwonlydefs)
    actual.update(dict(zip(reversed(named), reversed(defs))))
    actual.update(dict(zip(named, args)))

    if vargs:
        actual[vargs] = tuple(args[len(named):])

    actual.update(kwargs)

    for name, value in actual.items():
        if value is nonce:
            raise TypeError("%s missing required positional argument: '%s'" % (func.__name__, name))

    return tuple_of_dict(actual)

def tuple_of_dict(dictionary, name="Args"):
    assert isinstance(dictionary, dict), "dictionary must be a dict instance"
    return namedtuple(name, dictionary.keys())(**dictionary)

def arg_count(func):
    named, vargs, _, defs, kwonly, kwonlydefs, _ = getfullargspec(func)
    return len(named) + len(kwonly) + (1 if vargs else 0)

def condition(description, predicate, precondition=False, postcondition=False, instance=False):
    assert isinstance(description, str), "contract descriptions must be strings"
    assert len(description) > 0, "contracts must have nonempty descriptions"
    assert isfunction(predicate), "contract predicates must be functions"
    assert not iscoroutinefunction(predicate), "contract predicates cannot be coroutines"
    assert precondition or postcondition, "contracts must be at least one of pre- or post-conditional"
    if instance or precondition:
        assert arg_count(predicate) == 1, "invariant predicates must take one argument"
    elif postcondition:
        assert arg_count(predicate) in (2, 3), "postcondition predicates must take two or three arguments"

    def require(f):
        wrapped = get_wrapped_func(f)

        if iscoroutinefunction(f):
            @wraps(f)
            async def inner(*args, **kwargs):
                rargs = build_call(f, *args, **kwargs) if not instance else args[0]

                if precondition and not predicate(rargs):
                    raise PreconditionError(description)

                preserved_values = {}
                for preserver in getattr(wrapped, "__contract_preserver__", [lambda x: {}]):
                    preserved_values.update(preserver(rargs))
                result = await f(*args, **kwargs)

                if instance:
                    if not predicate(rargs):
                        raise PostconditionError(description)
                elif postcondition:
                    check = None
                    if arg_count(predicate) == 3:
                        check = predicate(rargs, result, tuple_of_dict(preserved_values))
                    else:
                        check = predicate(rargs, result)
                    if not check:
                        raise PostconditionError(description)

                return result

        elif isfunction(f):
            @wraps(f)
            def inner(*args, **kwargs):
                rargs = build_call(f, *args, **kwargs) if not instance else args[0]

                if precondition and not predicate(rargs):
                    raise PreconditionError(description)

                preserved_values = {}
                for preserver in getattr(wrapped, "__contract_preserver__", [lambda x: {}]):
                    preserved_values.update(preserver(rargs))
                result = f(*args, **kwargs)

                if instance:
                    if not predicate(rargs):
                        raise PostconditionError(description)
                elif postcondition:
                    check = None
                    if arg_count(predicate) == 3:
                        check = predicate(rargs, result, tuple_of_dict(preserved_values))
                    else:
                        check = predicate(rargs, result)
                    if not check:
                        raise PostconditionError(description)

                return result

        else:
            raise NotImplementedError

        inner.__contract_wrapped_func__ = wrapped
        return inner
    return require

def require(arg1, arg2=None):
    """
    Specify a precondition described by `description` and tested by
    `predicate`.
    """

    assert (isinstance(arg1, str) and isfunction(arg2)) or (isfunction(arg1) and arg2 is None)

    description = ""
    predicate = lambda x: x

    if isinstance(arg1, str):
        description = arg1
        predicate = arg2
    else:
        description = get_function_source(arg1)
        predicate = arg1

    return condition(description, predicate, True, False)

def rewrite(args, **kwargs):
    return args._replace(**kwargs)

def preserve(preserver):
    assert isfunction(preserver), "preservers must be functions"
    assert arg_count(preserver) == 1, "preservers can only take a single argument"

    def func(f):
        wrapped = get_wrapped_func(f)
        @wraps(f)
        def inner(*args, **kwargs):
            return f(*args, **kwargs)
        if not hasattr(wrapped, "__contract_preserver__"):
            wrapped.__contract_preserver__ = []
        wrapped.__contract_preserver__.append(preserver)
        return inner
    return func
            
def transform(transformer):
    assert isfunction(transformer), "transformers must be functions"
    assert arg_count(transformer) == 1, "transformers can only take a single argument"

    def func(f):
        @wraps(f)
        def inner(*args, **kwargs):
            rargs = transformer(build_call(f, *args, **kwargs))
            return f(**(rargs._asdict()))
        return inner
    return func

def types(**requirements):
    """
    Specify a precondition based on the types of the function's
    arguments.
    """

    def predicate(args):
        for name, kind in sorted(requirements.items()):
            assert hasattr(args, name), "missing required argument `%s`" % name

            if not isinstance(kind, tuple):
                kind = (kind,)

            if not any(isinstance(getattr(args, name), k) for k in kind):
                return False

        return True

    return condition("the types of arguments must be valid", predicate, True)

def ensure(arg1, arg2=None):
    """
    Specify a precondition described by `description` and tested by
    `predicate`.
    """

    assert (isinstance(arg1, str) and isfunction(arg2)) or (isfunction(arg1) and arg2 is None)

    description = ""
    predicate = lambda x: x

    if isinstance(arg1, str):
        description = arg1
        predicate = arg2
    else:
        description = get_function_source(arg1)
        predicate = arg1

    return condition(description, predicate, False, True)

def invariant(arg1, arg2=None):
    """
    Specify a class invariant described by `description` and tested
    by `predicate`.
    """

    desc = ""
    predicate = lambda x: x

    if isinstance(arg1, str):
        desc = arg1
        predicate = arg2
    else:
        desc = get_function_source(arg1)
        predicate = arg1

    def invariant(c):
        def check(name, func):
            exceptions = ("__getitem__", "__setitem__", "__lt__", "__le__", "__eq__",
                          "__ne__", "__gt__", "__ge__", "__init__")

            if name.startswith("__") and name.endswith("__") and name not in exceptions:
                return False

            if not ismethod(func) and not isfunction(func):
                return False

            if getattr(func, "__self__", None) is c:
                return False

            return True

        class InvariantContractor(c):
            pass

        for name, value in [(name, getattr(c, name)) for name in dir(c)]:
            if check(name, value):
                setattr(InvariantContractor, name,
                        condition(desc, predicate, name != "__init__", True, True)(value))
        return InvariantContractor
    return invariant

if not __debug__:
    def require(description, predicate):
        def func(f):
            return f
        return func

    def ensure(description, predicate):
        def func(f):
            return f
        return func

    def invariant(description, predicate):
        def func(c):
            return c
        return func

    def transform(transformer):
        def func(c):
            return c
        return func

    def preserve(preserver):
        def func(c):
            return c
        return func

if __name__ == "__main__":
    import doctest
    doctest.testmod()
