import unittest
from hammer.proof.utils import unicode_escape


class TestUnicodeEscape(unittest.TestCase):
    def test_ascii_characters(self):
        # Test with basic ASCII characters
        input_str = "Hello World"
        self.assertEqual(unicode_escape(input_str), "Hello World")

    def test_unicode_characters(self):
        # Test with Unicode characters
        input_str = "Hello 世界"  # Chinese characters
        self.assertEqual(unicode_escape(input_str), "Hello \\u4e16\\u754c")

    def test_special_characters(self):
        # Test with special characters
        input_str = "π ≤ ∞"  # Mathematical symbols
        self.assertEqual(unicode_escape(input_str), "\\u03c0 \\u2264 \\u221e")

    def test_empty_string(self):
        # Test with empty string
        self.assertEqual(unicode_escape(""), "")


if __name__ == "__main__":
    unittest.main()
