#include <iostream>
#include <errno.h>
#include <stdio.h>
#include <sys/types.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdexcept>
#include <getopt.h>

#include "config.h"

#ifdef HAVE_UNISTD_H

#include <unistd.h>

#endif

#if defined(__FreeBSD__)
#include <sys/param.h>
#endif

#include "int64.h"
#include "atacmds.h"
#include "dev_interface.h"
#include "ataprint.h"
#include "knowndrives.h"
#include "scsicmds.h"
#include "scsiprint.h"
#include "nvmeprint.h"
#include "smartctl.h"
#include "utility.h"

const char *smartctl_cpp_cvsid = "$Id$"
  CONFIG_H_CVSID SMARTCTL_H_CVSID;

// Globals to control printing
bool printing_is_switchable = false;
bool printing_is_off = true;
std::string errmsg;

static void printslogan() {
  pout("%s\n", format_version_info("smartctl").c_str());
}

static void UsageSummary() {
  pout("\nUse smartctl -h to get a usage summary\n\n");
  return;
}

static std::string getvalidarglist(int opt);

// Values for  --long only options, see parse_options()
enum {
    opt_identify = 1000, opt_scan, opt_scan_open, opt_set, opt_smart
};

/* Returns a string containing a formatted list of the valid arguments
   to the option opt or empty on failure. Note 'v' case different */
static std::string getvalidarglist(int opt) {
  switch (opt) {
    case 'q':
      return "errorsonly, silent, noserial";
    case 'd':
      return smi()->get_valid_dev_types_str() + ", auto, test";
    case 'T':
      return "normal, conservative, permissive, verypermissive";
    case 'b':
      return "warn, exit, ignore";
    case 'r':
      return "ioctl[,N], ataioctl[,N], scsiioctl[,N], nvmeioctl[,N]";
    case opt_smart:
    case 'o':
    case 'S':
      return "on, off";
    case 'l':
      return "error, selftest, selective, directory[,g|s], "
        "xerror[,N][,error], xselftest[,N][,selftest], "
        "background, sasphy[,reset], sataphy[,reset], "
        "scttemp[sts,hist], scttempint,N[,p], "
        "scterc[,N,M], devstat[,N], ssd, "
        "gplog,N[,RANGE], smartlog,N[,RANGE], "
        "nvmelog,N,SIZE";
    case 'P':
      return "use, ignore, show, showall";
    case 't':
      return "offline, short, long, conveyance, force, vendor,N, select,M-N, "
        "pending,N, afterselect,[on|off]";
    case 'F':
      return std::string(get_valid_firmwarebug_args()) + ", swapid";
    case 'n':
      return "never, sleep, standby, idle";
    case 'f':
      return "old, brief, hex[,id|val]";
    case 'g':
      return "aam, apm, lookahead, security, wcache, rcache, wcreorder, wcache-sct";
    case opt_set:
      return "aam,[N|off], apm,[N|off], lookahead,[on|off], security-freeze, "
        "standby,[N|off|now], wcache,[on|off], rcache,[on|off], wcreorder,[on|off[,p]], "
        "wcache-sct,[ata|on|off[,p]]";
    case 's':
      return getvalidarglist(opt_smart) + ", " + getvalidarglist(opt_set);
    case opt_identify:
      return "n, wn, w, v, wv, wb";
    case 'v':
    default:
      return "";
  }
}

// Checksum error mode
enum checksum_err_mode_t {
    CHECKSUM_ERR_WARN, CHECKSUM_ERR_EXIT, CHECKSUM_ERR_IGNORE
};

static checksum_err_mode_t checksum_err_mode = CHECKSUM_ERR_WARN;

static void scan_devices(const smart_devtype_list &types, bool with_open, char **argv);


// Printing function (controlled by global printing_is_off)
// [From GLIBC Manual: Since the prototype doesn't specify types for
// optional arguments, in a call to a variadic function the default
// argument promotions are performed on the optional argument
// values. This means the objects of type char or short int (whether
// signed or not) are promoted to either int or unsigned int, as
// appropriate.]
void pout(const char *fmt, ...) {
  va_list ap;

  // initialize variable argument list
  va_start(ap, fmt);
  if (printing_is_off) {
    va_end(ap);
    return;
  }

  // print out
  vprintf(fmt, ap);
  va_end(ap);
  fflush(stdout);
  return;
}

// Globals to set failuretest() policy
bool failuretest_conservative = false;
unsigned char failuretest_permissive = 0;

// Compares failure type to policy in effect, and either exits or
// simply returns to the calling routine.
// Used in ataprint.cpp and scsiprint.cpp.
void failuretest(failure_type type, int returnvalue) {
  // If this is an error in an "optional" SMART command
  if (type == OPTIONAL_CMD) {
    if (!failuretest_conservative)
      return;
    pout("An optional SMART command failed: exiting. Remove '-T conservative' option to continue.\n");
    EXIT(returnvalue);
  }

  // If this is an error in a "mandatory" SMART command
  if (type == MANDATORY_CMD) {
    if (failuretest_permissive--)
      return;
    pout("A mandatory SMART command failed: exiting. To continue, add one or more '-T permissive' options.\n");
    EXIT(returnvalue);
  }

  throw std::logic_error("failuretest: Unknown type");
}

// Used to warn users about invalid checksums. Called from atacmds.cpp.
// Action to be taken may be altered by the user.
void checksumwarning(const char *string) {
  // user has asked us to ignore checksum errors
  if (checksum_err_mode == CHECKSUM_ERR_IGNORE)
    return;

  pout("Warning! %s error: invalid SMART checksum.\n", string);

  // user has asked us to fail on checksum errors
  if (checksum_err_mode == CHECKSUM_ERR_EXIT) EXIT(FAILSMART);
}

// Return info string about device protocol
static const char *get_protocol_info(const smart_device *dev) {
  switch ((int) dev->is_ata()
          | ((int) dev->is_scsi() << 1)
          | ((int) dev->is_nvme() << 2)) {
    case 0x1:
      return "ATA";
    case 0x2:
      return "SCSI";
    case 0x3:
      return "ATA+SCSI";
    case 0x4:
      return "NVMe";
    default:
      return "Unknown";
  }
}

// Device scan
// smartctl [-d type] --scan[-open] -- [PATTERN] [smartd directive ...]
void scan_devices(const smart_devtype_list &types, bool with_open, char **argv) {
  bool dont_print = !(ata_debugmode || scsi_debugmode || nvme_debugmode);

  const char *pattern = 0;
  int ai = 0;
  if (argv[ai] && argv[ai][0] != '-')
    pattern = argv[ai++];

  smart_device_list devlist;
  printing_is_off = dont_print;
  bool ok = smi()->scan_smart_devices(devlist, types, pattern);
  printing_is_off = false;

  if (!ok) {
    pout("# scan_smart_devices: %s\n", smi()->get_errmsg());
    return;
  }

  for (unsigned i = 0; i < devlist.size(); i++) {
    smart_device_auto_ptr dev(devlist.release(i));

    if (with_open) {
      printing_is_off = dont_print;
      dev.replace(dev->autodetect_open());
      printing_is_off = false;

      if (!dev->is_open()) {
        pout("# %s -d %s # %s, %s device open failed: %s\n", dev->get_dev_name(),
             dev->get_dev_type(), dev->get_info_name(),
             get_protocol_info(dev.get()), dev->get_errmsg());
        continue;
      }
    }

    pout("%s -d %s", dev->get_dev_name(), dev->get_dev_type());
    if (!argv[ai])
      pout(" # %s, %s device\n", dev->get_info_name(), get_protocol_info(dev.get()));
    else {
      for (int j = ai; argv[j]; j++)
        pout(" %s", argv[j]);
      pout("\n");
    }

    if (dev->is_open())
      dev->close();
  }
}


static int main_worker(const char *name) {
  // Throw if runtime environment does not match compile time test.
  check_config();

  // Initialize interface
  smart_interface::init();
  if (!smi())
    return 1;

  // Parse input arguments
  ata_print_options ataopts;
  scsi_print_options scsiopts;
  nvme_print_options nvmeopts;
  const char *type = 0;
  smart_device_auto_ptr dev;

  ataopts.smart_check_status = scsiopts.smart_check_status = nvmeopts.smart_check_status = true;
  scsiopts.smart_ss_media_log = true;

  // get device of appropriate type
  dev = smi()->get_smart_device(name, type);

  if (!dev) {
    pout("%s: %s\n", name, smi()->get_errmsg());
    errmsg = smi()->get_errmsg();
    return FAILCMD;
  }


  if (dev->is_ata() && ataopts.powermode >= 2 && dev->is_powered_down()) {
    pout("%s: Device is in %s mode, exit(%d)\n", dev->get_info_name(), "STANDBY (OS)", FAILPOWER);
    errmsg = "low power mode";
    return FAILPOWER;
  }

  // Open device
  {
    // Save old info
    smart_device::device_info oldinfo = dev->get_info();

    // Open with autodetect support, may return 'better' device
    dev.replace(dev->autodetect_open());

    // Report if type has changed
    if ((ata_debugmode || scsi_debugmode || nvme_debugmode)
        && oldinfo.dev_type != dev->get_dev_type())
      pout("%s: Device open changed type from '%s' to '%s'\n",
           dev->get_info_name(), oldinfo.dev_type.c_str(), dev->get_dev_type());
  }
  if (!dev->is_open()) {
    pout("Smartctl open device: %s failed: %s\n", dev->get_info_name(), dev->get_errmsg());
    errmsg = dev->get_errmsg();
    return FAILDEV;
  }

  // now call appropriate ATA or SCSI routine
  int retval = 0;
  if (dev->is_ata())
    retval = ataPrintMain(dev->to_ata(), ataopts);
  else if (dev->is_scsi())
    retval = scsiPrintMain(dev->to_scsi(), scsiopts);
  else if (dev->is_nvme())
    retval = nvmePrintMain(dev->to_nvme(), nvmeopts);
  else {
    // we should never fall into this branch!
    pout("%s: Neither ATA, SCSI nor NVMe device\n", dev->get_info_name());
    errmsg = "error device type";
  }


  dev->close();
  return retval;
}

int health_check(const char *name) {
  errmsg = "";
  int status;
  try {
    // Do the real work ...
    status = main_worker(name);
  }
  catch (int ex) {
    // EXIT(status) arrives here
    status = ex;
  }
  catch (const std::bad_alloc & /*ex*/) {
    // Memory allocation failed (also thrown by std::operator new)
//    printf("Smartctl: Out of memory\n");
    errmsg = "Out of memory";
    status = FAILCMD;
  }
  catch (const std::exception &ex) {
    // Other fatal errors
//    printf("Smartctl: Exception: %s\n", ex.what());
    errmsg = ex.what();
    status = FAILCMD;
  }
  return status;
}

using namespace std;

int main(int argc, char **argv) {
  if (argc != 2) {
    cout << "*flag*:bad_arg" << endl;
    cout << "*errmsg*:Argument error" << endl;
    return 0;
  }
  errmsg = "";
  const char *name = argv[argc - 1];
  int status = health_check(name);

  cout << "*flag*:";
  if (status & FAILCMD) { cout << ("fail_cmd,"); }
  if (status & FAILDEV) { cout << ("fail_dev,"); }
  if (status & FAILPOWER) { cout << ("fail_power,"); }
  if (status & FAILID) { cout << ("fail_id,"); }
  if (status & FAILSMART) { cout << ("fail_smart,"); }
  if (status & FAILSTATUS) { cout << ("fail_status,"); }
  if (status & FAILATTR) { cout << ("fail_attr,"); }
  if (status & FAILAGE) { cout << ("fail_age,"); }
  if (status & FAILERR) { cout << ("fail_err,"); }
  if (status & FAILLOG) { cout << ("fail_log,"); }
  if (status & HEALTH_PASSED) { cout << ("health_passed,"); }
  if (status & HEALTH_FAILED) { cout << ("health_failed,"); }
  cout << endl;
  cout <<"*errmsg*:"<< errmsg << endl;
}