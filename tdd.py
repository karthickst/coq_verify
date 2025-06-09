import unittest
from trade_position_system import TradePositionSystem, TradePosition

class TestTradePositionSystem(unittest.TestCase):
    def test_open_position(self):
        system = TradePositionSystem()
        position_id = system.open_position("AAPL", 100.0, 10)
        self.assertIsNotNone(position_id)
        self.assertEqual(len(system.get_positions()), 1)

    def test_close_position(self):
        system = TradePositionSystem()
        position_id = system.open_position("AAPL", 100.0, 10)
        system.close_position(position_id)
        self.assertEqual(len(system.get_positions()), 0)

    def test_close_non_existent_position(self):
        system = TradePositionSystem()
        with self.assertRaises(ValueError):
            system.close_position("non-existent-id")

    def test_get_positions(self):
        system = TradePositionSystem()
        position_id1 = system.open_position("AAPL", 100.0, 10)
        position_id2 = system.open_position("GOOG", 500.0, 5)
        positions = system.get_positions()
        self.assertEqual(len(positions), 2)
        self.assertEqual(positions[position_id1].symbol, "AAPL")
        self.assertEqual(positions[position_id2].symbol, "GOOG")

if __name__ == '__main__':
    unittest.main()
