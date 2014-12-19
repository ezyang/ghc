import qualified Map

main = do
    print (Map.toList (Map.insert "foo" "bar" Map.empty))
