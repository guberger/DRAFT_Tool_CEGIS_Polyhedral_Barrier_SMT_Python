def get_val_int(model, s):
    return int(model[s].as_long())

def get_val_real(model, s):
    return float(model[s].as_fraction())