#include <satbmc.hh>

SATBMCFalsification::SATBMCFalsification(IModel& model)
  : MCAlgorithm(model)
{
  logger << "Creating SATBMCFalsification algorithm instance "
         << get_param("alg_name") << " @" << this
         << endl;
}

SATBMCFalsification::~SATBMCFalsification()
{
  logger << "Destroying SATBMCFalsification algorithm instance"
         << get_param("alg_name") << " @" << this
         << endl;
}

void SATBMCFalsification::operator()()
{
  assert(0);
}
