#Utility functions for database operations for Jsonl files
import jsonlines
import os
import pprint

db = 'mathlib_data_bluebench.jsonl'

### General Utility Functions ###

def check_db_exists(db: str = db):
    """
    Check if the database file exists.
    """
    assert type(db) == str, "Database name must be a string."
    if not os.path.exists(db):
        print(f"Database {db} does not exist.")
        return False
    return True

def get_object_index(index: int = 0, db: str = db):
    """
    Get the object at the specified index from the database.
    """
    if not check_db_exists(db) : return None
    with jsonlines.open(db) as reader:
        for i, obj in enumerate(reader):
            if i == index:
                return obj
    print(f"Index {index} out of range.")
    return None


def get_db_list(db: str = db):
    """
    Read the database file and return a list of objects.
    """
    if not check_db_exists(db) : return None
    with jsonlines.open(db, mode='r') as reader:
        return [obj for obj in reader]

def print_objects(n :int = 1, db: str = db, pp : bool = True):
    """
    Print the first `number` objects from the database.
    """
    if not check_db_exists(db) : return None
     
    with jsonlines.open(db) as reader:
        for i, obj in enumerate(reader):
            if i >= n:
                break
            print(i+1)
            if pp:
                pprint.pprint(obj)
            else:
                print(obj)


def get_object_name(name: str, db: str = db):
    """
    Get the object with the specified name from the database.
    """
    if not check_db_exists(db) : return None
    assert type(name) == str, "Name must be a string."

    with jsonlines.open(db) as reader:
        for obj in reader:
            if obj.get('name') == name:
                return obj

def get_object_name_from_list_dic(name : str, list_dic: list[dict]):
    """
    Get the object with the specified name from a list of dictionaries.
    """
    assert type(name) == str, "Name must be a string."
    assert type(list_dic) == list, "List must be a list."
    assert type(list_dic[0]) == dict, "List must contain dictionaries."

    for obj in list_dic:
        if obj.get('name') == name:
            return obj
    raise ValueError(f"Object with name '{name}' not found in the list of dictionaries.")


def rename_key_db(old_key : str, new_key : str , db : str = db):
    """
    Rename a key in all objects in the database.
    """
    if not check_db_exists(db) : return None
    assert type(old_key) == type(new_key) == type(db) == str, "Keys and db must be strings."

    if old_key == new_key:
        print("Old key and new key are the same. No changes made.")
        return
    
    if old_key not in get_object_index(0, db):
        print(f"Key '{old_key}' does not exist in the database. No changes made.")
        return
    
    with jsonlines.open(db, mode='r') as reader:
        with jsonlines.open('temp_' + db, mode='w') as writer:
            for obj in reader:
                if old_key in obj:
                    obj[new_key] = obj.pop(old_key)
                writer.write(obj)
    os.remove(db)
    os.rename('temp_' + db, db)
    print(f"Renamed key '{old_key}' to '{new_key}' in database {db}.")


def add_key_val_db(key: str, value, db: str = db):
    """
    Add a key-value pair to all objects in the database.
    """
    if not check_db_exists(db) : return None
    assert type(key) == str, "Key and value must be strings."

    if key in get_object_index(0, db):
        print(f"Key '{key}' already exists in the database. No changes made.")
        return

    with jsonlines.open(db, mode='r') as reader:
        with jsonlines.open('temp_' + db, mode='w') as writer:
            for obj in reader:
                obj[key] = value
                writer.write(obj)
    os.remove(db)
    os.rename('temp_' + db, db)
    print(f"Added key '{key}' with value '{value}' to all objects in database {db}.")

def remove_key_db(key: str, db: str = db):
    """
    Remove a key from all objects in the database.
    """
    if not check_db_exists(db) : return None
    assert type(key) == str, "Key must be a string."

    if key not in get_object_index(0, db):
        print(f"Key '{key}' does not exist in the database. No changes made.")
        return

    with jsonlines.open(db, mode='r') as reader:
        with jsonlines.open('temp_' + db, mode='w') as writer:
            for obj in reader:
                if key in obj:
                    del obj[key]
                writer.write(obj)
    os.remove(db)
    os.rename('temp_' + db, db)
    print(f"Removed key '{key}' from all objects in database {db}.")

    
def get_parents_depth(name_list, db_list : list, start_depth = 0, final_depth: int = 1):
    """
    Get the depth of the parent-child relationships in the database.
    """
    if not check_db_exists(db) : return None
    assert type(start_depth) == type(final_depth) == int, "Depth must be an integer."
    assert 0 <= start_depth <= final_depth, "Depth must be non-negative."
    assert type(name_list) in [str, list, set], "Object must be a dictionary."
    
    if type(name_list) == str: name_list = [name_list]    
    if start_depth == final_depth: return
    
    print_list = []
    print('Depth:', start_depth + 1)
    for name in name_list:
        obj = get_object_name_from_list_dic(name, db_list)
        print_list += obj['parent']
    print_list = set(print_list)
    print(print_list)
    get_parents_depth(print_list, db_list, start_depth + 1, final_depth)








