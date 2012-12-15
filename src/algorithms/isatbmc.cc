#include <isatbmc.hh>

ISATBMCFalsification::ISATBMCFalsification(IModel& model, Expr_ptr property)
    : SATBMCFalsification(model, property)
{}

ISATBMCFalsification::~ISATBMCFalsification()
{}
