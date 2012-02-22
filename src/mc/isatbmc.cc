#include <isatbmc.hh>

ISATBMCAlgorithm::ISATBMCAlgorithm(Model& model)
  : MCAlgorithm(model)
{
  logger << "Creating ISATBMC algorithm instance "
         << get_param("alg_name") << " @" << this
         << endl;
}

ISATBMCAlgorithm::~ISATBMCAlgorithm()
{
  logger << "Destroying ISATBMC algorithm instance"
         << get_param("alg_name") << " @" << this
         << endl;
}
