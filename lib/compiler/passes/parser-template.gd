# this is the default parser template. overwrite with -p
# @generated by PeggyGD __VERSION__.
extends JSParser
class_name __CLAZZ_NAME__

##GLOBALS##

##TABLES##

##EXPRESSIONS##

func parse(source: PEG.Source, options = {})->PEG.Result:
##START_RULES##
  return super(source, options)
