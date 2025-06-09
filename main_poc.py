//Main POC  

class TradePosition:
    def __init__(self, symbol, entry_price, quantity):
        self.symbol = symbol
        self.entry_price = entry_price
        self.quantity = quantity

class TradePositionSystem:
    def __init__(self):
        self.positions = {}
        self.position_id_counter = 0

    def open_position(self, symbol, entry_price, quantity):
        self.position_id_counter += 1
        position_id = str(self.position_id_counter)
        self.positions[position_id] = TradePosition(symbol, entry_price, quantity)
        return position_id

    def close_position(self, position_id):
        if position_id not in self.positions:
            raise ValueError("Position does not exist")
        del self.positions[position_id]

    def get_positions(self):
        return self.positions
