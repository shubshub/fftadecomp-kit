"""Import cycles among tools modules: no new one, and no member reads another while importing.

Inside an import cycle, which member finishes importing first depends on which one was
imported first. A module-level read of another member (`X = other.NAME`,
`class C(other.Base)`, `from other import NAME`) then works or fails by import order:
#344, #370 and #371 were each this failure.

The check is static. It parses tools/*.py and builds the graph of the imports that run
at import time. Two things fail it:

1. An import cycle with a member outside KNOWN_CYCLE: a new cycle, or a new member of
   the one that exists. A member that leaves the cycle fails nothing.

2. A read, at import time, of another member of the module's own cycle:

   * `alias.NAME` on another member, after `import other` or `import other as alias`, or
     through a module-level re-binding `m = alias`;
   * `from other import ...`, including `*`;
   * `getattr`, `hasattr` or `vars` with another member as the first argument.

"At import time" covers module and class bodies, compound statements, the first iterable
of a generator expression, and each function's decorators, defaults and annotations. It
also follows module-level calls into the same module: the body of a called function, the
`__init__` and `__new__` of an instantiated class, and the body of a decorator function,
transitively. Generator and async functions are not followed, because calling them does
not run their bodies. The body of `if __name__ == "__main__":` is excluded.

An import inside a function is therefore no edge of the graph, and a cycle that exists
only through such imports fails nothing: every module of it finishes importing before
the function runs. The exception is a function that module-level code calls: its imports
and the reads in its body count like module-level ones.

Known misses: calls through attributes (`self.helper()`, `other_module.f()`), so a
function that another module calls at import time is not followed; the inner function of
a decorator factory; and imports made with `importlib`. Other indirect paths are missed
too: `__import__` at module level, `sys.modules["x"].NAME`, `operator.attrgetter`,
re-binding other than `m = alias` (tuple, annotated or walrus assignment, a dict of
modules), a function passed as a value (`map(f, ...)`, `functools.partial(f)`) rather
than called by name, a function defined under a module-level `if` or nested in a
followed function, and inherited or generated methods (`__init_subclass__`, a base
class's `__init__`, a dataclass `default_factory`). Known conservative reports: a module
that imports the other member only after its own definitions (the "import at the bottom"
idiom) can work in both orders, but its read is still reported; an import under
`if TYPE_CHECKING:` is an edge; and `other.__file__`, which a partly imported module
already has, and `except other.Error:`, evaluated only when an exception is raised, are
reported. When this test was added, no module of a cycle used any of these forms at
import time.
"""
import ast
from pathlib import Path
import sys
import tempfile
import textwrap
import unittest

TOOLS = Path(__file__).resolve().parents[1] / "tools"
KNOWN_CYCLE = frozenset((
    "descriptor_partial_word_prerequisite", "framed_switch_inventory", "literal_callback_closure_profile",
    "local_descriptor_copy_prerequisite", "menu_runner_switches", "menu_selection_switches",
    "multiple_switch_native_profile", "multiple_switch_owner_prerequisite", "owner_admission_profile",
    "scheduler_copy_state", "transfer_task_constructor", "tree_two_word_callback_closure_profile",
    "two_word_callback_closure_profile"))
ATTRIBUTE_READERS = ("getattr", "hasattr", "vars")


def main_guard(node):
    """node is `if __name__ == "__main__":`."""
    test = node.test
    return (isinstance(test, ast.Compare) and isinstance(test.left, ast.Name) and test.left.id == "__name__"
            and len(test.ops) == 1 and isinstance(test.ops[0], ast.Eq) and len(test.comparators) == 1
            and isinstance(test.comparators[0], ast.Constant) and test.comparators[0].value == "__main__")


def runs_when_called(function):
    """Calling function runs its body: it is neither async nor a generator."""
    if isinstance(function, ast.AsyncFunctionDef):
        return False
    stack = list(function.body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.Yield, ast.YieldFrom)):
            return False
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
            stack.extend(ast.iter_child_nodes(node))
    return True


def import_time_nodes(tree):
    """The nodes evaluated when the module is imported (see the module docstring)."""
    definitions = {node.name: node for node in tree.body
                   if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))}
    followed = set()

    def called(name):
        target = definitions.get(name)
        if target is None or target.name in followed:
            return []
        followed.add(target.name)
        if isinstance(target, ast.ClassDef):
            return [statement for method in target.body
                    if isinstance(method, ast.FunctionDef) and method.name in ("__init__", "__new__")
                    for statement in method.body]
        return list(target.body) if runs_when_called(target) else []

    stack = list(tree.body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            for decorator in node.decorator_list:
                if isinstance(decorator, ast.Name):
                    stack += called(decorator.id)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            arguments = node.args
            stack += node.decorator_list + arguments.defaults + [d for d in arguments.kw_defaults if d]
            stack += [a.annotation for a in (*arguments.posonlyargs, *arguments.args, *arguments.kwonlyargs,
                                             arguments.vararg, arguments.kwarg) if a and a.annotation]
            stack += [node.returns] if node.returns else []
            continue
        if isinstance(node, ast.Lambda):
            stack += node.args.defaults + [d for d in node.args.kw_defaults if d]
            continue
        if isinstance(node, ast.GeneratorExp):
            stack.append(node.generators[0].iter)
            continue
        if isinstance(node, ast.If) and main_guard(node):
            stack += node.orelse
            continue
        yield node
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            stack += called(node.func.id)
        stack.extend(ast.iter_child_nodes(node))


def imported_modules(node, modules):
    """The modules of the directory that node names, when node is an import statement."""
    if isinstance(node, ast.Import):
        return [alias.name for alias in node.names if alias.name in modules]
    if isinstance(node, ast.ImportFrom) and node.level == 0 and node.module in modules:
        return [node.module]
    return []


def import_graph(directory):
    """(syntax tree, import-time nodes, modules imported at import time), each by module
    name, for the modules of directory."""
    modules = {path.stem: ast.parse(path.read_bytes(), str(path)) for path in sorted(Path(directory).glob("*.py"))}
    nodes = {name: list(import_time_nodes(tree)) for name, tree in modules.items()}
    edges = {name: {target for node in nodes[name] for target in imported_modules(node, modules)}
             for name in modules}
    return modules, nodes, edges


def import_cycles(edges):
    """The strongly connected components of edges that have more than one module."""
    return [component for component in strongly_connected(edges) if len(component) > 1]


def unknown_cycles(directory, known):
    """The import cycles of the modules of directory that have a member outside known,
    each as a sorted list of its members."""
    return sorted(sorted(component) for component in import_cycles(import_graph(directory)[2])
                  if not component <= known)


def cycle_reads(directory):
    """(module, line, read) for each import-time read of another member of the module's
    import cycle, in the modules of directory."""
    modules, nodes, edges = import_graph(directory)
    aliases, imported_names = {}, {}
    for name in modules:
        aliases[name], imported_names[name] = {}, []
        for node in nodes[name]:
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name in modules:
                        aliases[name][alias.asname or alias.name] = alias.name
            elif imported_modules(node, modules):
                imported_names[name].append((node.lineno, node.module, [a.name for a in node.names]))
        rebound = True
        while rebound:  # `m = alias` makes m an alias too
            rebound = False
            for node in nodes[name]:
                if (isinstance(node, ast.Assign) and isinstance(node.value, ast.Name)
                        and node.value.id in aliases[name]):
                    for target in node.targets:
                        if isinstance(target, ast.Name) and target.id not in aliases[name]:
                            aliases[name][target.id] = aliases[name][node.value.id]
                            rebound = True
    findings = []
    for component in import_cycles(edges):
        for name in sorted(component):
            others = component - {name}
            for node in nodes[name]:
                if (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name)
                        and aliases[name].get(node.value.id) in others):
                    findings.append((name, node.lineno, f"{node.value.id}.{node.attr}"))
                elif (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                        and node.func.id in ATTRIBUTE_READERS and node.args
                        and isinstance(node.args[0], ast.Name) and aliases[name].get(node.args[0].id) in others):
                    findings.append((name, node.lineno, f"{node.func.id}({node.args[0].id}, ...)"))
            for line, module, names in imported_names[name]:
                if module in others:
                    findings.append((name, line, f"from {module} import {', '.join(names)}"))
    return sorted(set(findings))


def strongly_connected(edges):
    """Tarjan's algorithm, iterative: the strongly connected components of edges."""
    index, low, on_stack, stack, components = {}, {}, set(), [], []
    for root in edges:
        if root in index:
            continue
        work = [(root, iter(sorted(edges[root])))]
        index[root] = low[root] = len(index)
        stack.append(root)
        on_stack.add(root)
        while work:
            node, successors = work[-1]
            for successor in successors:
                if successor not in index:
                    index[successor] = low[successor] = len(index)
                    stack.append(successor)
                    on_stack.add(successor)
                    work.append((successor, iter(sorted(edges[successor]))))
                    break
                if successor in on_stack:
                    low[node] = min(low[node], index[successor])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[node])
                if low[node] == index[node]:
                    component = set()
                    while True:
                        member = stack.pop()
                        on_stack.discard(member)
                        component.add(member)
                        if member == node:
                            break
                    components.append(component)
    return components


class ImportCycleTests(unittest.TestCase):
    def test_no_tools_module_reads_its_import_cycle_at_import_time(self):
        self.assertEqual(cycle_reads(TOOLS), [])

    def test_no_tools_import_cycle_has_a_member_outside_the_known_cycle(self):
        self.assertEqual(unknown_cycles(TOOLS, KNOWN_CYCLE), [],
                         "import cycles among module-level imports with a member outside KNOWN_CYCLE")

    def check(self, sources, checker=cycle_reads):
        with tempfile.TemporaryDirectory() as directory:
            for name, text in sources.items():
                (Path(directory) / f"{name}.py").write_text(textwrap.dedent(text))
            return checker(directory)

    def b_reads(self, body):
        """The findings for a two-module cycle a <-> b, with body after b's `import a`."""
        return self.check({"a": "import b\nVALUE = 1\nBase = object\nT = int\ndef hook(f): return f\n",
                           "b": "import a\n" + body})

    def test_each_direct_import_time_read_inside_a_cycle_is_reported(self):
        cases = {
            "VALUE = a.VALUE\n": [("b", 2, "a.VALUE")],
            "class C:\n    X = a.VALUE\n": [("b", 3, "a.VALUE")],
            "class C(a.Base):\n    pass\n": [("b", 2, "a.Base")],
            "def f(x=a.VALUE):\n    return x\n": [("b", 2, "a.VALUE")],
            "def f(*, x=a.VALUE):\n    return x\n": [("b", 2, "a.VALUE")],
            "@a.hook\ndef f():\n    pass\n": [("b", 2, "a.hook")],
            "def f(x: a.Base) -> a.T:\n    return x\n": [("b", 2, "a.Base"), ("b", 2, "a.T")],
            "def f(x: a.Base, /):\n    return x\n": [("b", 2, "a.Base")],
            "def f(*args: a.Base, **kw: a.T):\n    return args\n": [("b", 2, "a.Base"), ("b", 2, "a.T")],
            "if True:\n    VALUE = [a.VALUE for _ in ()]\n": [("b", 3, "a.VALUE")],
            "f = lambda x=a.VALUE: x\n": [("b", 2, "a.VALUE")],
            "f = lambda *, x=a.VALUE: x\n": [("b", 2, "a.VALUE")],
            "G = (x for x in a.VALUE)\n": [("b", 2, "a.VALUE")],
            "VALUE = getattr(a, 'VALUE')\n": [("b", 2, "getattr(a, ...)")],
            "PRESENT = hasattr(a, 'VALUE')\n": [("b", 2, "hasattr(a, ...)")],
            "NAMES = vars(a)\n": [("b", 2, "vars(a, ...)")],
            "m = a\nVALUE = m.VALUE\n": [("b", 3, "m.VALUE")],
            "m = a\nn = m\nX = n.VALUE\n": [("b", 4, "n.VALUE")],
            "X = a.Base.mro\n": [("b", 2, "a.Base")],
            "if __name__ != '__main__':\n    X = a.VALUE\n": [("b", 3, "a.VALUE")],
            "if __name__ == 'other':\n    X = a.VALUE\n": [("b", 3, "a.VALUE")],
        }
        for body, expected in cases.items():
            with self.subTest(body=body):
                self.assertEqual(self.b_reads(body), expected)
        self.assertEqual(self.b_reads("from a import VALUE\n"), [("b", 2, "from a import VALUE")])
        self.assertEqual(self.b_reads("from a import *\n"), [("b", 2, "from a import *")])
        self.assertEqual(self.check({"a": "import b\nVALUE = 1\n", "b": "import a as alias\nVALUE = alias.VALUE\n"}),
                         [("b", 2, "alias.VALUE")])
        # A longer cycle a -> c -> b -> a.
        self.assertEqual(self.check({"a": "import c\nVALUE = 1\n", "c": "import b\n",
                                     "b": "import a\nVALUE = a.VALUE\n"}), [("b", 2, "a.VALUE")])

    def test_reads_behind_module_level_calls_into_the_same_module_are_reported(self):
        cases = {
            "def get():\n    return a.VALUE\nX = get()\n": [("b", 3, "a.VALUE")],
            "def inner():\n    return a.VALUE\ndef outer():\n    return inner()\nX = outer()\n":
                [("b", 3, "a.VALUE")],
            "def deco(f):\n    a.VALUE\n    return f\n@deco\ndef g():\n    pass\n": [("b", 3, "a.VALUE")],
            "def deco(c):\n    a.VALUE\n    return c\n@deco\nclass C:\n    pass\n": [("b", 3, "a.VALUE")],
            "class K:\n    def __init__(self):\n        self.v = a.VALUE\nINSTANCE = K()\n": [("b", 4, "a.VALUE")],
            "class K:\n    def __new__(cls):\n        return a.VALUE\nINSTANCE = K()\n": [("b", 4, "a.VALUE")],
            "class K:\n    X = 1\n    def get(self):\n        return a.VALUE\nY = K.X\n": [],
            "def get():\n    return a.VALUE\ndef twice():\n    return get(), get()\nX = twice()\n":
                [("b", 3, "a.VALUE")],
            "def f():\n    return g()\ndef g():\n    return f(), a.VALUE\nX = f()\n": [("b", 5, "a.VALUE")],
            "def f():\n    def g():\n        yield\n    return a.VALUE\nX = f()\n": [("b", 5, "a.VALUE")],
        }
        for body, expected in cases.items():
            with self.subTest(body=body):
                self.assertEqual(self.b_reads(body), expected)

    def test_reads_outside_a_cycle_or_import_time_are_not_reported(self):
        for body in ("def f():\n    return a.VALUE\n",
                     "async def f():\n    return a.VALUE\n",
                     "class C:\n    def f(self):\n        return a.VALUE\n",
                     "f = lambda: a.VALUE\n",
                     "G = (a.VALUE for _ in range(3))\n",
                     "G = (x for x in () for y in a.VALUE)\n",
                     "def gen():\n    yield a.VALUE\nG = gen()\n",
                     "async def co():\n    return a.VALUE\nC = co()\n",
                     "class K:\n    def method(self):\n        return a.VALUE\nINSTANCE = K()\n",
                     "if __name__ == '__main__':\n    print(a.VALUE)\n"):
            with self.subTest(body=body):
                self.assertEqual(self.b_reads(body), [])
        # No cycle: a does not import b.
        self.assertEqual(self.check({"a": "VALUE = 1\n", "b": "import a\nVALUE = a.VALUE\n"}), [])
        # An import inside a function is no import-time edge, so there is no cycle.
        self.assertEqual(self.check({"a": "def f():\n    import b\nVALUE = 1\n",
                                     "b": "import a\nVALUE = a.VALUE\n"}), [])
        # c is outside the cycle a <-> b, so b's read of it is none.
        self.assertEqual(self.check({"a": "import b\n", "b": "import a\nimport c\nVALUE = c.VALUE\n",
                                     "c": "VALUE = 1\n"}), [])
        # Modules outside the directory are ignored.
        self.assertEqual(self.check({"a": "import b\nimport os\nSEP = os.sep\n", "b": "import a\n"}), [])
        # The else branch of a __main__ guard still runs at import time.
        self.assertEqual(self.b_reads("if __name__ == '__main__':\n    pass\nelse:\n    X = a.VALUE\n"),
                         [("b", 5, "a.VALUE")])

    def test_import_cycles_are_found_and_compared_with_the_known_members(self):
        later = "def f():\n    import a\n"
        cases = (
            ({"a": "import b\n", "b": "import a\n"}, [["a", "b"]]),
            ({"a": "import c\n", "c": "from b import f\n", "b": "import a\ndef f(): pass\n"}, [["a", "b", "c"]]),
            ({"a": "import b\n", "b": "import a\n", "c": "import d\n", "d": "import c\nimport a\n",
              "e": "import a\n"}, [["a", "b"], ["c", "d"]]),
            ({"a": "import os, b\n", "b": "class C:\n    import a\n"}, [["a", "b"]]),
            ({"a": "import b\n", "b": "try:\n    import a\nexcept ImportError:\n    pass\n"}, [["a", "b"]]),
            # Run by a module-level call, the import in the function is an import-time one.
            ({"a": "import b\n", "b": later + "f()\n"}, [["a", "b"]]),
            # An import that runs later closes no cycle.
            ({"a": "import b\n", "b": later}, []),
            ({"a": "import b\n", "b": "class C:\n    def f(self):\n        from a import VALUE\n"}, []),
            ({"a": "import b\n", "b": "if __name__ == '__main__':\n    import a\n"}, []),
            ({"a": "import b\n", "b": "def gen():\n    import a\n    yield a\nG = gen()\n"}, []),
            ({"a": "import b\nimport c\n", "b": "import c\n", "c": "import os\n"}, []),
            ({"a": "import a\n"}, []),
        )
        for sources, expected in cases:
            with self.subTest(sources=sources):
                self.assertEqual(self.check(sources, lambda directory: unknown_cycles(directory, frozenset())),
                                 expected)
        sources = {"a": "import b\n", "b": "import c\n", "c": "import a\n", "d": "import e\n", "e": "import d\n"}
        for known, expected in (("a b c d e", []), ("a b c d e f", []), ("a b c", [["d", "e"]]),
                                ("a b d e", [["a", "b", "c"]]), ("", [["a", "b", "c"], ["d", "e"]])):
            with self.subTest(known=known):
                self.assertEqual(self.check(sources, lambda directory: unknown_cycles(directory,
                                                                                      frozenset(known.split()))),
                                 expected)

    def test_a_read_behind_a_function_level_import_is_reported_only_when_the_function_runs(self):
        body = "def get():\n    import a\n    return a.VALUE\n"
        self.assertEqual(self.check({"a": "import b\nVALUE = 1\n", "b": body}), [])
        self.assertEqual(self.check({"a": "import b\nVALUE = 1\n", "b": body + "X = get()\n"}),
                         [("b", 3, "a.VALUE")])
        self.assertEqual(self.check({"a": "import b\nVALUE = 1\n", "b": "def get():\n    from a import VALUE\n    "
                                     "return VALUE\nX = get()\n"}), [("b", 2, "from a import VALUE")])


if __name__ == "__main__":
    sys.exit(unittest.main())
