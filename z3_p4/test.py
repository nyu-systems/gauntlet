import unittest


class Z3Tests(unittest.TestCase):

    def test_key_bmv2(self):
        import key_bmv2
        self.assertEqual(key_bmv2.z3_check(), 0)

    def test_equality_bmv2(self):
        import equality_bmv2
        self.assertEqual(equality_bmv2.z3_check(), 0)

    def test_basic_routing_bmv2(self):
        import basic_routing_bmv2
        self.assertEqual(basic_routing_bmv2.z3_check(), 0)

    def test_strength3(self):
        import strength3
        self.assertEqual(strength3.z3_check(), 0)


if __name__ == '__main__':
    unittest.main()
