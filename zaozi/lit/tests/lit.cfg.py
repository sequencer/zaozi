import platform
import lit.formats
from lit.llvm import llvm_config
from lit.llvm.subst import ToolSubst

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ScalaCliTest import ScalaCliTest

config.name = 'ZAOZI'
config.test_format = ScalaCliTest(True)
config.suffixes = [".scala", ".sc"]
config.substitutions = [
    ('%SCALAVERSION', config.scala_version),
    ('%RUNCLASSPATH', ':'.join(config.run_classpath)),
    ('%JAVAHOME', config.java_home),
    ('%JAVALIBRARYPATH', ':'.join(config.java_library_path))
]
config.test_source_root = os.path.dirname(__file__)
