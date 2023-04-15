using SHA, Tar, Pkg

#########################
function main()::Nothing
#########################

  filename = "utils.tar.bz2"
  temp_dir = "temp"

  if ispath( temp_dir )
    rm( temp_dir; force=true, recursive=true )
  end # if

  open(`$(Pkg.PlatformEngines.exe7z()) x $filename -so`) do io
    Tar.extract(io, temp_dir, copy_symlinks = Pkg.PlatformEngines.copy_symlinks())
  end

  calc_hash = open(temp_dir) do file
    bytes2hex(sha256(file))
  end

  println( "git-tree-sha1: ", bytes2hex(sha1(calc_hash)) )
  println( "sha256: ", bytes2hex(open(sha256, filename)) )

  rm( temp_dir; force=true, recursive=true )

  return nothing

end # function main

########
main()
########
