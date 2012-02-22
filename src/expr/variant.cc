#include <variant.hh>

bool Variant::is_boolean()
{ return f_type == BOOLEAN; }
bool Variant::as_boolean()
{ return f_bool; }

bool Variant::is_integer()
{ return f_type == INTEGER; }
int Variant::as_integer()
{ return f_int; }

bool Variant::is_string()
{ return f_type == STRING; }
string Variant::as_string()
{ return f_str; }
