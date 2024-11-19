import unittest
from hammer.lean.server import LeanServer


class TestLeanServer(unittest.TestCase):
    def setUp(self):
        self.server = LeanServer()

    def test_init(self):
        """Test that server initializes properly"""
        self.assertIsNotNone(self.server.proc)

    def test_run_code_basic(self):
        """Test running basic Lean code"""
        result = self.server.run_code("#eval 1 + 1")
        self.assertEqual(result["messages"][0]["data"], "2")
        self.assertEqual(result["env"], 0)

    def test_run_code_basic_with_env(self):
        """Test running basic Lean code"""
        result = self.server.run_code("def f := 2")
        self.assertEqual(result["env"], 0)
        result = self.server.run_code("#eval f + 2", env=0)
        self.assertEqual(result["messages"][0]["data"], "4")
        self.assertEqual(result["env"], 1)
        result = self.server.run_code("#eval 2 + 2", env=1)
        self.assertEqual(result["env"], 2)

    def tearDown(self):
        """Clean up after tests"""
        self.server.proc.close()


class TestLeanServerWithMathlib(unittest.TestCase):
    def setUp(self):
        self.server = LeanServer(True)

    def test_init(self):
        """Test that server initializes properly"""
        self.assertIsNotNone(self.server.proc)

    def test_run_code_basic(self):
        """Test running basic Lean code"""
        result = self.server.run_code("open Nat", env=0)
        result = self.server.run_code(
            "theorem h0\n (f : \u2124 \u2192 \u2124)\n (h : (\u2200 a b, f (2 * a) + (2 * f b) = f (f (a + b)))) :\n\u2200 b, f 0 + 2 * f b = f (f b):= by\n intro b\n specialize h 0 b\n simp at h\n exact h",
            env=1,
        )
        self.assertEqual(result["env"], 2)

    def test_run_code_basic_with_error(self):
        """Test running basic Lean code"""
        result = self.server.run_code("open Nat", env=0)
        result = self.server.run_code(
            "theorem h0\n (f : \u2124 \u2192 \u2124)\n (h : (\u2200 a b, f (2 * a) + (2 * f b) = f (f (a + b)))) :\n\u2200 b, f 0 + 2 * f b = f (f b):= by\n intro b\n specialize h 0 b\n simp at h",
            env=1,
        )
        self.assertEqual(
            result["messages"][0]["data"],
            "unsolved goals\nf : ℤ → ℤ\nb : ℤ\nh : f 0 + 2 * f b = f (f b)\n⊢ f 0 + 2 * f b = f (f b)",
        )
        self.assertEqual(result["env"], 2)

    def tearDown(self):
        """Clean up after tests"""
        self.server.proc.close()


if __name__ == "__main__":
    unittest.main()
