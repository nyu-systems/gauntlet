import unittest


class Z3Tests(unittest.TestCase):

    def test_basic_routing_bmv2(self):
        import basic_routing_bmv2
        self.assertEqual(basic_routing_bmv2.z3_check(), 0)

    def test_equality_bmv2(self):
        import equality_bmv2
        self.assertEqual(equality_bmv2.z3_check(), 0)

    def test_issue1544_bmv2(self):
        import issue1544_bmv2
        self.assertEqual(issue1544_bmv2.z3_check(), 0)

    def test_issue1595(self):
        import issue1595
        self.assertEqual(issue1595.z3_check(), 0)

    def test_issue1863_bmv2(self):
        import issue1863_bmv2
        self.assertNotEqual(issue1863_bmv2.z3_check(), 0)

    def test_issue1985(self):
        import issue1985
        self.assertEqual(issue1985.z3_check(), 0)

    def test_issue983(self):
        import issue983
        self.assertEqual(issue983.z3_check(), 0)

    def test_key_bmv2(self):
        import key_bmv2
        self.assertEqual(key_bmv2.z3_check(), 0)

    def test_strength3(self):
        import strength3
        self.assertEqual(strength3.z3_check(), 0)


if __name__ == '__main__':
    unittest.main()
