#include <variant.hh>

Variant NilValue;

bool Variant::is_nil() const
{ return f_type == BOTTOM; }

bool Variant::is_boolean() const
{ return f_type == BOOLEAN; }
bool Variant::as_boolean() const
{ return f_bool; }

bool Variant::is_integer() const
{ return f_type == INTEGER; }
int Variant::as_integer() const
{ return f_int; }

bool Variant::is_string() const
{ return f_type == STRING; }
string Variant::as_string() const
{ return f_str; }

ostream& operator<<(ostream& os, const Variant& variant)
{
  if (variant.is_boolean()) {
    return os << variant.as_boolean();
  }
  else assert(0);
}
