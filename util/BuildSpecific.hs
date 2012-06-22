module BuildSpecific where

-- ====================================================================
-- Everytime you make a distribution you need to edit the following

shortVersion = "1.5.1"
version = "Omega Interpreter: version " ++ shortVersion

distrDir home = home ++ "/Omega/distr/"

rootDir home = home ++ "/omega/"
srcDir home = rootDir home ++ "src/"
utilDir home = rootDir home ++ "util/"
parseDir home = rootDir home ++ "src/"
libDir home = rootDir home ++ "src/"
manualDir home = rootDir home ++ "doc/"
testsDir home = rootDir home ++ "tests/"

extension = ""
