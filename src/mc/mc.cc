#include <mc.hh>

MCAlgorithm::MCAlgorithm(Model& model)
  : f_mm(ModelMgr::INSTANCE())
  , f_em(ExprMgr::INSTANCE())
  , f_tm(TypeMgr::INSTANCE())
  , f_model(model)
  , f_traces()
{
  logger << "Creating MC algoritm instance "
         << get_param("alg_name")
         << " @" << this
         << endl;
}

MCAlgorithm::~MCAlgorithm()
{
  logger << "Destroying MC algoritm instance"
         << get_param("alg_name")
         << " @" << this
         << endl;
}
