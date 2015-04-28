AC_PREREQ([2.67])
AC_INIT([], [0], [jobredeaux@gatech.edu])

# PVS

AC_CHECK_PROG(PVS,pvs,pvs,no)
if test "$PVS" = no ; then
   enable_pvs_support=no
   AC_MSG_ERROR(Cannot find pvs.)
   reason_pvs_support=" (pvs not found)"
else
   PVSLIB=`$PVS -where`
   AC_MSG_CHECKING(PVS version)
   PVSVERSION=`$PVS -version | sed -n -e 's|.*Version* *\([[^ ]]*\)$|\1|p' `
   case $PVSVERSION in
          6.*)
	        enable_pvs_support=yes
                AC_MSG_RESULT($PVSVERSION)
                ;;
          *)
                AC_MSG_RESULT($PVSVERSION)
                enable_pvs_support=no
	        AC_MSG_ERROR(You need PVS 6.0 or higher)
                reason_pvs_support=" (need version 6.0 or higher)"
                ;;
    esac
fi

# Nasalib

AC_MSG_CHECKING([for NASA PVS library])
enable_pvs_libs=no
reason_pvs_libs=" (no NASA PVS library in PVS_LIBRARY_PATH)"
for dir in  `echo $PVS_LIBRARY_PATH | tr ':' ' '`; do
   if test -f $dir/nasalib-version; then
      enable_pvs_libs=yes
      reason_pvs_libs=""
   fi
done
AC_MSG_RESULT($enable_pvs_libs)
if test -f "$enable_pvs_libs"=yes ; then
   AC_MSG_ERROR(Cannot find NASA PVS library in PVS_LIBRARY_PATH)
fi

# Why3

AC_CHECK_PROG(WHY3,why3,why3,no)
if test "$WHY3" = no ; then
   AC_MSG_ERROR(Cannot find Why3.)
else
	AC_MSG_CHECKING(why3 version)
	WHY3_VERSION=`$WHY3 --version | sed -n -e 's|.*version *\([[^ ]]*\).*$|\1|p'`
	case $WHY3_VERSION in
	     0.83*) 
	     	     AC_MSG_RESULT($WHY3_VERSION)
		     ;;
	     *)
		     AC_MSG_RESULT($WHY3_VERSION)
		     AC_MSG_ERROR(You need Why3 version 0.83)
		     ;;
        esac
fi   

# Frama-C
AC_CHECK_PROG(FRAMAC,frama-c,frama-c,no)
if test "$FRAMAC" = no ; then
     AC_MSG_ERROR(Cannot find Frama-C.)
     enable_frama_c="no"
     reason_frama_c=" (frama-c not found)"
else
   AC_MSG_CHECKING(Frama-C version)
   FRAMAC_VERSION=`$FRAMAC -version | sed -n -e 's|Version: *\(.*\)$|\1|p'`
   AC_MSG_RESULT($FRAMAC_VERSION)
   case $FRAMAC_VERSION in
      Neon-*) ;;
      *) AC_MSG_ERROR(Version Neon required.)
         enable_frama_c=no
         reason_frama_c=" (version Neon required)"
         ;;
   esac
fi

AC_CONFIG_FILES([compile-lisp.sh], [chmod +x compile-lisp.sh])
AC_OUTPUT