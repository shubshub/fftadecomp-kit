"""Bounded callback declarations count pointers, never callback argument words."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import volatile_semantics as sem

class CallbackParameterTests(unittest.TestCase):
    def signature(self,text):return sem.function_signature(sem.file_scope(text),'callee')
    def test_named_and_abstract_callbacks(self):
        for callback in ('unsigned int (*callback)(void *,void *,void *)',
                         'unsigned int (*)(void *,void *,void *)',
                         'void (*callback)(double, long long)',
                         'double (*callback)(int,int)',
                         'long long (*)(double,double)',
                         'int (* const callback)(int, void (*)(int,int))'):
            with self.subTest(callback=callback):
                self.assertEqual(self.signature('extern void *callee('+callback+', unsigned short size, void *descriptor, void *parent);'),(True,4))
    def test_direct_callback_typedef(self):
        for parameter in ('Callback callback','Callback'):
            self.assertEqual(self.signature('typedef unsigned int (*Callback)(void *,void *,void *); extern void callee('+parameter+', int);'),(False,2))
    def test_disagreement_outer_arity(self):
        with self.assertRaises(sem.SemanticError):self.signature('void callee(void (*)(int,int)); void callee(void (*)(int,int),int);')
    def test_fail_closed_declarations(self):
        for declaration in ('struct X x','double x','long long x','int array[2]','Unknown x',
                            'void (*cb[2])(int)','void (**cb)(int)', 'void (*cb)(int,)',
                            'void (*cb)(int', 'void (*cb)(...)', 'int x,', 'int x = 0', 'int *x*', 'int x*', 'int double', 'double int'):
            with self.subTest(declaration=declaration),self.assertRaises(sem.SemanticError):
                self.signature('void callee('+declaration+');')
    def test_unknown_and_ambiguous_typedefs(self):
        for prefix in ('typedef int Callback;', 'typedef int (*Callback)(int); typedef int Callback;',
                       'typedef int (*Callback)(int), Other;', 'typedef int Callback(int);'):
            with self.subTest(prefix=prefix),self.assertRaises(sem.SemanticError):self.signature(prefix+' void callee(Callback);')
    def test_callback_nesting_bound(self):
        callback='void (*)(int)'
        for _ in range(9):callback='void (*)('+callback+')'
        with self.assertRaises(sem.SemanticError):self.signature('void callee('+callback+');')

    def test_unbalanced_extra_parens_and_implicit_return_refused(self):
        for declaration in ('void callee(int));','void callee((int));','callee(int);'):
            with self.subTest(declaration=declaration),self.assertRaises(sem.SemanticError):
                self.signature(declaration)

    def test_variable_arity_and_unprototyped_stay_unknown(self):
        for text in ('void callee();','void callee(int,...);'):
            self.assertEqual(self.signature(text),(False,None))

if __name__=='__main__':unittest.main()
