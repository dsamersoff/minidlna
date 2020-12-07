/* MiniDLNA project
 *
 * http://sourceforge.net/projects/minidlna/
 *
 * MiniDLNA media server
 * Copyright (C) 2008-2012  Justin Maggard
 *
 * This file is part of MiniDLNA.
 *
 * MiniDLNA is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2 as
 * published by the Free Software Foundation.
 *
 * MiniDLNA is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with MiniDLNA. If not, see <http://www.gnu.org/licenses/>.
 *
 * Portions of the code from the MiniUPnP project:
 *
 * Copyright (c) 2006-2007, Thomas Bernard
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * The name of the author may not be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <sys/file.h>
#include <sys/time.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <time.h>
#include <signal.h>
#include <errno.h>
#include <pthread.h>
#include <limits.h>
#include <libgen.h>
#include <pwd.h>
#include <grp.h>

#include "config.h"

#ifdef ENABLE_NLS
#include <locale.h>
#include <libintl.h>
#endif

#include "event.h"
#include "upnpglobalvars.h"
#include "sql.h"
#include "upnphttp.h"
#include "upnpdescgen.h"
#include "minidlnapath.h"
#include "getifaddr.h"
#include "upnpsoap.h"
#include "options.h"
#include "utils.h"
#include "minissdp.h"
#include "minidlnatypes.h"
#include "process.h"
#include "upnpevents.h"
#include "scanner.h"
#include "monitor.h"
#include "libav.h"
#include "log.h"
#include "tivo_beacon.h"
#include "tivo_utils.h"
#include "avahi.h"
#include "mtools.h"

#if SQLITE_VERSION_NUMBER < 3005001
# warning "Your SQLite3 library appears to be too old!  Please use 3.5.1 or newer."
# define sqlite3_threadsafe() 0
#endif

unsigned char
png_sm_test[] =   "\x89\x50\x4e\x47\x0d\x0a\x1a\x0a\x00\x00\x00\x0d\x49\x48\x44\x52\x00\x00\x00\x30\x00\x00\x00\x30"
             "\x08\x06\x00\x00\x00\x57\x02\xf9\x87\x00\x00\x00\x19\x74\x45\x58\x74\x53\x6f\x66\x74\x77\x61\x72"
             "\x65\x00\x41\x64\x6f\x62\x65\x20\x49\x6d\x61\x67\x65\x52\x65\x61\x64\x79\x71\xc9\x65\x3c\x00\x00"
             "\x03\x22\x69\x54\x58\x74\x58\x4d\x4c\x3a\x63\x6f\x6d\x2e\x61\x64\x6f\x62\x65\x2e\x78\x6d\x70\x00"
             "\x00\x00\x00\x00\x3c\x3f\x78\x70\x61\x63\x6b\x65\x74\x20\x62\x65\x67\x69\x6e\x3d\x22\xef\xbb\xbf"
             "\x22\x20\x69\x64\x3d\x22\x57\x35\x4d\x30\x4d\x70\x43\x65\x68\x69\x48\x7a\x72\x65\x53\x7a\x4e\x54"
             "\x63\x7a\x6b\x63\x39\x64\x22\x3f\x3e\x20\x3c\x78\x3a\x78\x6d\x70\x6d\x65\x74\x61\x20\x78\x6d\x6c"
             "\x6e\x73\x3a\x78\x3d\x22\x61\x64\x6f\x62\x65\x3a\x6e\x73\x3a\x6d\x65\x74\x61\x2f\x22\x20\x78\x3a"
             "\x78\x6d\x70\x74\x6b\x3d\x22\x41\x64\x6f\x62\x65\x20\x58\x4d\x50\x20\x43\x6f\x72\x65\x20\x35\x2e"
             "\x33\x2d\x63\x30\x31\x31\x20\x36\x36\x2e\x31\x34\x35\x36\x36\x31\x2c\x20\x32\x30\x31\x32\x2f\x30"
             "\x32\x2f\x30\x36\x2d\x31\x34\x3a\x35\x36\x3a\x32\x37\x20\x20\x20\x20\x20\x20\x20\x20\x22\x3e\x20"
             "\x3c\x72\x64\x66\x3a\x52\x44\x46\x20\x78\x6d\x6c\x6e\x73\x3a\x72\x64\x66\x3d\x22\x68\x74\x74\x70"
             "\x3a\x2f\x2f\x77\x77\x77\x2e\x77\x33\x2e\x6f\x72\x67\x2f\x31\x39\x39\x39\x2f\x30\x32\x2f\x32\x32"
             "\x2d\x72\x64\x66\x2d\x73\x79\x6e\x74\x61\x78\x2d\x6e\x73\x23\x22\x3e\x20\x3c\x72\x64\x66\x3a\x44"
             "\x65\x73\x63\x72\x69\x70\x74\x69\x6f\x6e\x20\x72\x64\x66\x3a\x61\x62\x6f\x75\x74\x3d\x22\x22\x20"
             "\x78\x6d\x6c\x6e\x73\x3a\x78\x6d\x70\x3d\x22\x68\x74\x74\x70\x3a\x2f\x2f\x6e\x73\x2e\x61\x64\x6f"
             "\x62\x65\x2e\x63\x6f\x6d\x2f\x78\x61\x70\x2f\x31\x2e\x30\x2f\x22\x20\x78\x6d\x6c\x6e\x73\x3a\x78"
             "\x6d\x70\x4d\x4d\x3d\x22\x68\x74\x74\x70\x3a\x2f\x2f\x6e\x73\x2e\x61\x64\x6f\x62\x65\x2e\x63\x6f"
             "\x6d\x2f\x78\x61\x70\x2f\x31\x2e\x30\x2f\x6d\x6d\x2f\x22\x20\x78\x6d\x6c\x6e\x73\x3a\x73\x74\x52"
             "\x65\x66\x3d\x22\x68\x74\x74\x70\x3a\x2f\x2f\x6e\x73\x2e\x61\x64\x6f\x62\x65\x2e\x63\x6f\x6d\x2f"
             "\x78\x61\x70\x2f\x31\x2e\x30\x2f\x73\x54\x79\x70\x65\x2f\x52\x65\x73\x6f\x75\x72\x63\x65\x52\x65"
             "\x66\x23\x22\x20\x78\x6d\x70\x3a\x43\x72\x65\x61\x74\x6f\x72\x54\x6f\x6f\x6c\x3d\x22\x41\x64\x6f"
             "\x62\x65\x20\x50\x68\x6f\x74\x6f\x73\x68\x6f\x70\x20\x43\x53\x36\x20\x28\x57\x69\x6e\x64\x6f\x77"
             "\x73\x29\x22\x20\x78\x6d\x70\x4d\x4d\x3a\x49\x6e\x73\x74\x61\x6e\x63\x65\x49\x44\x3d\x22\x78\x6d"
             "\x70\x2e\x69\x69\x64\x3a\x31\x31\x41\x44\x31\x44\x42\x34\x30\x35\x33\x36\x31\x31\x45\x33\x42\x33"
             "\x30\x35\x46\x32\x34\x46\x35\x45\x44\x32\x46\x30\x31\x31\x22\x20\x78\x6d\x70\x4d\x4d\x3a\x44\x6f"
             "\x63\x75\x6d\x65\x6e\x74\x49\x44\x3d\x22\x78\x6d\x70\x2e\x64\x69\x64\x3a\x31\x31\x41\x44\x31\x44"
             "\x42\x35\x30\x35\x33\x36\x31\x31\x45\x33\x42\x33\x30\x35\x46\x32\x34\x46\x35\x45\x44\x32\x46\x30"
             "\x31\x31\x22\x3e\x20\x3c\x78\x6d\x70\x4d\x4d\x3a\x44\x65\x72\x69\x76\x65\x64\x46\x72\x6f\x6d\x20"
             "\x73\x74\x52\x65\x66\x3a\x69\x6e\x73\x74\x61\x6e\x63\x65\x49\x44\x3d\x22\x78\x6d\x70\x2e\x69\x69"
             "\x64\x3a\x31\x31\x41\x44\x31\x44\x42\x32\x30\x35\x33\x36\x31\x31\x45\x33\x42\x33\x30\x35\x46\x32"
             "\x34\x46\x35\x45\x44\x32\x46\x30\x31\x31\x22\x20\x73\x74\x52\x65\x66\x3a\x64\x6f\x63\x75\x6d\x65"
             "\x6e\x74\x49\x44\x3d\x22\x78\x6d\x70\x2e\x64\x69\x64\x3a\x31\x31\x41\x44\x31\x44\x42\x33\x30\x35"
             "\x33\x36\x31\x31\x45\x33\x42\x33\x30\x35\x46\x32\x34\x46\x35\x45\x44\x32\x46\x30\x31\x31\x22\x2f"
             "\x3e\x20\x3c\x2f\x72\x64\x66\x3a\x44\x65\x73\x63\x72\x69\x70\x74\x69\x6f\x6e\x3e\x20\x3c\x2f\x72"
             "\x64\x66\x3a\x52\x44\x46\x3e\x20\x3c\x2f\x78\x3a\x78\x6d\x70\x6d\x65\x74\x61\x3e\x20\x3c\x3f\x78"
             "\x70\x61\x63\x6b\x65\x74\x20\x65\x6e\x64\x3d\x22\x72\x22\x3f\x3e\xbc\x68\x2a\x2f\x00\x00\x07\x21"
             "\x49\x44\x41\x54\x78\xda\xec\x5a\x7b\x6c\x14\x45\x18\x9f\x7d\xdc\x6b\xef\x5a\x68\xef\xfa\x80\x56"
             "\xc0\xa0\x2d\x94\x2a\x46\x24\x90\x62\x48\xd4\x04\x88\x0f\xa0\x36\x24\x10\x14\x9a\x40\x40\x13\xa2"
             "\xc4\x08\x86\x47\xa5\x8d\x60\x05\x8d\xe0\x2b\x28\xd8\x04\x09\x04\x22\x41\x29\x46\x41\x0b\x54\x9b"
             "\x16\x45\xc5\x0a\x42\x83\x15\x09\x82\x4a\x6b\x1f\x96\xde\x75\xef\xb1\x8f\xf1\x9b\xb2\x57\xae\xdb"
             "\xdd\xbb\xdd\xbd\xfb\x87\xc8\x97\x4c\x66\x6f\x3b\x37\xf3\xfb\x7d\x8f\x99\xef\x9b\x2b\x85\x31\x46"
             "\xb7\xb2\xd0\xe8\x16\x97\x5b\x9e\x00\x65\x66\xf0\xa3\xc7\xda\xdf\x39\x50\xb0\x75\x99\x4b\x7c\x93"
             "\xa5\x50\x24\xb5\xe4\x65\x4a\x16\x7e\xc9\x10\x69\x86\xd9\xc7\xce\xee\x28\x4f\x39\x81\x59\xc7\x3a"
             "\x7d\xd0\xb5\xed\x1b\xdf\xca\x00\x78\xe4\x14\xdf\xe2\x1d\xd2\x21\x0e\xa1\xe4\x63\x48\xba\xec\xe1"
             "\x85\x73\x19\x1c\x90\x40\xf6\xbb\x79\x09\x31\x38\x97\x99\xd5\xd5\x99\x6a\x17\x3a\x04\x8d\x21\x0f"
             "\x18\xd9\x51\x90\x5d\xc5\xf5\xda\x0f\x23\x91\x9e\xc8\x5b\x56\x7a\xb7\x83\x0f\x7f\x95\x87\x84\xb3"
             "\x99\xfd\xe0\x15\x61\x94\xb5\x52\x17\x03\xa0\xfd\xe9\xd0\x4d\x1b\x6a\x75\x2f\x0a\xd8\xb6\x73\x7e"
             "\x7b\x8d\x2c\x53\xbe\xb0\xd1\x45\x71\x88\x09\x47\x1a\x72\xe5\x48\x63\x0e\x07\xcf\x5a\x43\xa6\x49"
             "\x47\xbd\xd3\x53\x69\x81\xfd\x71\x5d\x80\x1a\x4f\x83\x35\x1c\x3c\xbb\x2e\x02\xd6\x91\xe2\xf8\xb9"
             "\x24\xfc\xec\x8d\x80\xd6\x1d\x72\x8f\x9d\x4e\x66\x4d\xc3\x04\x40\xfb\x6b\xa0\x1b\x61\x64\xb2\x08"
             "\xf3\x98\xfd\xba\xa3\x8e\x09\x33\xf3\x82\x30\xf5\xcd\xe0\xc0\x08\x4b\x97\xd2\x82\xa1\x2f\xf2\x19"
             "\xe9\x8a\xdb\x6e\x50\x69\x23\xc0\x0a\x6b\x92\x0a\x62\x00\xef\x84\xae\x07\x9a\x23\xfa\x0e\x82\xd8"
             "\xd8\xee\x80\xbb\x91\x5b\xa8\xe8\xa3\x3b\x5b\x90\xf0\xa3\xcf\x8d\xc3\x8c\xa1\xef\x41\x10\x43\x14"
             "\x0c\x70\x27\x6e\x39\x1c\x02\x3a\x64\xd5\x02\xfb\x63\xc1\x9b\x11\x4c\x65\x76\x07\xec\xef\x95\x47"
             "\x9a\x72\xca\x01\xfc\xbf\x16\xe3\xdc\x91\xc8\x95\xa8\x38\xda\x2f\x82\xee\x9c\x7a\x8c\x01\x0b\x08"
             "\xd0\xb6\x64\xe4\x95\xac\x8f\x7d\x19\xdc\x36\x6a\x23\x74\xab\xa1\xd9\x4c\x58\xe0\x86\x03\x22\x54"
             "\x0c\x56\x68\x31\x6b\x81\x4f\x4d\x1e\x74\x64\xa1\xc3\xd0\x32\xd5\xe0\x89\xb8\x56\x5e\x21\xef\x32"
             "\x95\x31\x66\x0e\x0f\x4a\xc1\x62\xdc\x85\x40\xfb\x8b\xa1\x2b\x30\xb1\x08\xb1\x54\x11\x00\x9f\x03"
             "\x2d\xa0\x37\x08\x48\x04\xa0\xcd\x21\x63\x95\xef\x18\x95\x02\x08\xe8\xc5\x86\x5c\x08\xc0\x13\x52"
             "\xd7\xa1\x79\xb4\xbe\xa0\x72\xa1\x2e\x68\x4b\x00\x74\xad\x15\x07\x07\xb7\x22\x64\x6a\xa0\x79\xe3"
             "\xb8\x50\x54\x88\x62\x86\x81\x2b\xc9\x89\x2c\xb0\x5d\x0f\x7c\xec\x8e\x09\xad\x0a\x80\xfb\xac\x82"
             "\x57\x2c\x52\x0b\x8d\xa4\x28\x55\xca\x9c\xf1\xc4\xa3\x60\xd3\xb7\x00\x68\x9f\xec\xf7\x7f\xea\xb9"
             "\x16\x2f\x63\x5c\x3b\xe1\x37\xe2\x8f\x0b\x01\xf8\xc0\xd6\xb6\xe8\xc9\xd9\x1f\xc6\x0c\x13\xa1\x3d"
             "\xb7\xfb\x93\xc3\x43\x00\xc1\xb8\x37\xc8\xb6\x18\xfd\x0c\x63\x96\xc6\x58\x83\x6c\xd9\x7b\x6d\x05"
             "\x7c\x29\x45\x63\xbd\xd8\x23\xda\xcf\x07\x2b\x5c\x8b\xbe\x60\x35\x02\x77\x08\x78\x11\x2c\x7a\x8e"
             "\x97\xf8\xb6\x08\xe6\x00\x78\x99\xc6\xc4\x4b\x54\x9f\x8b\xa1\x3d\xa8\x31\xee\x79\xd5\x9a\x4b\x63"
             "\xac\x41\x14\x52\xf6\xf9\xc7\x3b\xf1\xfd\xdc\x6e\x3e\x9b\x6d\xe1\x74\x62\x96\x60\x9c\x3a\xc4\x85"
             "\x40\xfb\x33\xa0\x9b\xa2\xde\x56\x2e\x85\xe4\xd0\xf1\x1e\x11\x13\xf0\x26\xbc\x63\x1a\x68\x7b\x8d"
             "\x15\xb7\x8a\x60\x37\xfa\xae\xef\x59\xae\x3e\xb0\x16\xf7\xc9\x3e\xad\x03\x6c\x0a\x04\xf4\x0c\xad"
             "\x18\xd8\x13\x3b\xaa\x43\xc0\x22\x00\x17\x5a\x83\xb2\x13\x9b\xac\x1b\x14\xd9\x08\x24\x26\x59\x8d"
             "\x0f\xbf\x34\x82\x3a\xee\xdf\xe0\xfc\x81\x5f\x2a\x88\xd8\x21\xaa\xfe\xbc\x67\x10\x01\xd0\x7e\x25"
             "\x74\x59\x51\x3f\x6f\xec\x95\x82\xa7\x03\x12\x0b\xae\x63\x4b\xb2\xda\x3b\x01\x24\x9c\xc9\xd4\x0a"
             "\xd7\x84\x89\xb6\x23\xbd\x5b\xd8\xd6\xf0\xcc\x20\xbe\x99\x5f\x65\x81\x15\x2a\xfb\x17\x01\xf0\x24"
             "\xba\xd7\x12\x3f\x6f\x0e\x48\x7c\xc3\x75\x89\x0a\x48\xd8\x95\xa2\x3a\x2b\x1d\x5a\x7d\xb2\x93\x00"
             "\x70\x74\x21\xf4\xb8\xeb\x68\xef\x6b\x54\x9b\x50\x1c\xad\x3f\xd6\x02\x09\x0f\x0d\x61\x7d\xf0\x62"
             "\x48\x96\x88\x9f\xb7\x0b\xa6\xfc\x5c\x37\xbb\x56\xce\x91\xa8\x4c\x05\x2b\x54\xa4\x42\x1b\x02\xe8"
             "\xf5\x7b\x7e\x39\x57\xef\x5f\x87\x03\x72\xb6\x04\xc4\x0e\xd2\x7f\x8b\xa8\xe4\xa2\x75\x3f\xd7\x4b"
             "\x29\x1e\x52\xb6\xbc\xa8\x54\x01\x89\xc9\xa9\x2a\x9f\xfd\x72\x2e\x75\xc2\x5f\xe1\x6c\x69\x59\x50"
             "\x42\x3f\x95\xcf\x9d\x5c\x75\x97\x27\x94\xed\xa0\x53\x76\x41\x04\xfb\x7b\x33\x74\xeb\x55\xe7\xcd"
             "\x31\x94\x22\x25\x71\xed\x7d\x78\x72\x75\x63\x68\xe4\x56\xff\x49\x9a\xa6\x50\x59\x96\x9d\x66\x5e"
             "\x1c\xeb\xa1\xca\xef\xe0\x78\x17\x43\xa5\x8a\x44\x35\x74\x4d\xaa\x78\x60\x92\x99\x93\x0d\x8a\x68"
             "\x42\x4d\x33\xff\xc0\xe6\x26\xca\xd5\xc1\x33\x94\x8c\xcb\xe8\xd5\x13\x38\x92\x63\x6c\x22\x03\x8a"
             "\xd2\x58\xae\xb2\x30\x0d\xcf\xcc\x76\x04\xe9\xd4\xf0\x78\x58\x15\x0f\xd6\xee\x7e\x64\x8c\xc6\x1c"
             "\xb9\x18\x2c\x59\x5f\x8f\xbd\xe7\x3b\xa2\x71\xba\xc9\xfb\xd7\xae\x40\xff\x36\x0a\x24\x48\x2e\xd2"
             "\xa1\xd8\x9a\x7a\xc4\xe7\x70\x55\x15\xa6\x89\xc5\xe9\x36\x21\x49\x2b\x44\x34\xe2\xc1\x94\xf8\xce"
             "\xb6\x0b\x25\xeb\xea\xc5\x51\x75\x97\x5c\x08\x0f\xa4\x18\x1d\x00\xbe\x4a\x7d\x90\x2d\x1c\x54\x0a"
             "\xd1\x14\xbb\x28\xdf\x65\x7b\x09\xe2\x23\x37\x89\xf8\xd0\x88\x07\x43\xe2\xbe\x16\xc0\x93\x37\x35"
             "\x86\x8a\x76\x9d\xb1\x31\x61\x51\x9d\xf2\x2c\x1c\x72\x12\x83\x15\xea\xa0\x3b\xa5\x9e\xc8\x6b\xa7"
             "\x9d\x2f\x40\x7c\x2c\x19\xc5\xf1\x9c\xc5\xf8\xd0\x88\x07\x5d\xb1\xf5\x09\xa8\x78\xc7\x4f\xfc\xa4"
             "\xd7\x4f\x52\xae\x2e\x5e\xeb\x10\x3c\x05\xda\xaf\xd3\x4b\xe6\x4a\xf5\xb2\xd1\x42\x0f\xcb\x6d\x80"
             "\xf8\x08\xac\x5c\x71\x90\x68\xe0\x95\x6d\xef\xc6\xe6\x29\x35\x31\xcf\x3d\x71\xe2\xe1\x6d\x8d\x35"
             "\xfb\x65\xf9\xbd\x5b\xfb\xb3\xd1\xa9\x2f\x7f\x8d\x29\xac\x7b\x1e\xc9\x0a\x46\xfd\x82\x66\xcb\x79"
             "\xfe\x7d\x32\x9f\xee\x1e\xbc\x73\x75\xb4\x1e\xa8\x06\x12\x95\xa9\x88\x74\x00\x4f\xe6\x21\xc9\x9f"
             "\xfd\xd5\xae\x33\xf1\x86\x7e\x00\xda\x7f\x26\x11\x81\xb8\x15\x99\x42\x60\x50\x45\x06\x44\x6a\x2d"
             "\x02\x1f\x52\x91\xc5\x21\xd0\x5f\x91\x01\x01\x39\xe1\xad\x04\x90\x78\x9a\xb8\xae\x01\x02\xb1\x35"
             "\xf1\x3c\x20\x72\xc1\x20\xf0\x71\xd0\x1d\x50\xea\x86\x41\x12\x87\x40\x39\x80\xff\xc8\xf0\xb5\x0a"
             "\x90\xf8\x55\xab\xb0\xd7\x21\x10\x4d\x21\x3e\x53\xe2\x23\xa0\x03\x9c\x58\x75\x2f\xb4\x27\xf4\xd6"
             "\xd6\x21\xd0\x0a\xe0\x0b\xcd\x5e\xab\x94\x5a\xb8\xfe\x98\x0d\xad\xbb\x62\xe5\x8a\x8d\x1a\xe0\xc9"
             "\xbb\x6e\x65\x8c\xd9\xeb\x9a\x52\x4b\x57\x8b\x60\x05\x52\xbe\xcd\x35\x68\x01\xb5\x90\xdb\xb8\x65"
             "\xff\x9c\x18\x4b\x9e\x77\x40\xcb\x30\xf2\x25\x0d\x0b\xd4\x82\xf6\xe7\xea\xa6\x17\x09\xe6\x5b\xa0"
             "\xbe\x1b\x35\x2a\x4c\x98\xc9\xf0\x36\xe7\xec\x92\x21\xb9\xee\x64\x90\xdb\xe2\x06\x45\xee\x46\xe7"
             "\x27\xaa\x9a\x74\x05\x0e\x37\xb2\xd7\x6f\x30\x97\xb7\x50\x68\xf8\x79\x5f\x70\xe4\xf1\x31\xd8\xd1"
             "\xe5\x72\x8f\x8e\x20\xf7\x3d\x21\x84\x39\x19\x05\x2d\x10\xa8\x02\xed\x87\x2c\x13\x50\x48\x6c\x26"
             "\x95\x9d\xa1\xe3\xff\x6a\x5a\x24\xef\xcb\x3b\xa5\xb4\xcb\xc3\x20\x6f\xb9\xe9\x9e\x76\x78\x1e\x1f"
             "\x46\xae\xc2\x30\x92\x58\x9c\xf0\xfe\x67\xa0\x9a\x04\xf0\xd5\x09\x33\x54\x83\x93\x11\x33\x7e\xa3"
             "\x7b\x21\xdb\xe3\x90\x7d\xa7\x73\x05\x26\xc4\xc6\x75\x35\x8f\x8c\x98\x89\x21\xc4\x74\xb0\x28\x7c"
             "\xd5\x86\x6c\x38\xbe\x02\xe7\x1b\x2d\xbc\x91\x01\x2b\x34\x40\xd7\xa8\xe1\xe7\x28\xfb\xdb\x3c\x3e"
             "\xa7\x29\x9f\x4e\x04\x3e\x56\xb2\x44\xe4\xb8\x2f\x88\x68\x9f\x88\xf4\x7e\x5f\x6b\x02\xed\x37\x18"
             "\xaa\x11\x4c\xf8\x23\xd9\xca\xda\x08\xee\x7e\x3f\x6f\xf1\xf1\x9e\x3f\xd2\x49\xce\x62\xa9\x8e\x26"
             "\x9a\x1b\x2d\x20\x6e\xa4\x88\xd0\xef\x76\xc4\xf7\xd1\x37\xe6\xc1\xe4\x17\x2b\xd5\xce\x97\xb4\x05"
             "\x14\x2b\x74\x22\x19\x6f\x77\x5f\x4d\x27\x7e\x2e\x2b\xe0\x93\x16\xe2\x47\xe3\xc2\x88\x83\xf8\x90"
             "\xe1\x39\xe2\xa7\x6d\x7b\x40\xfb\x9d\x86\x37\x8d\xdb\xff\x2b\x71\x9b\xc0\xff\x9c\xc0\x7f\x02\x0c"
             "\x00\x12\xf6\xd3\x29\xcc\x5e\x35\x99\x00\x00\x00\x00\x49\x45\x4e\x44\xae\x42\x60\x82";

static LIST_HEAD(httplisthead, upnphttp) upnphttphead;

/* OpenAndConfHTTPSocket() :
 * setup the socket used to handle incoming HTTP connections. */
static int
OpenAndConfHTTPSocket(unsigned short port)
{
	int s;
	int i = 1;
	struct sockaddr_in listenname;

	/* Initialize client type cache */
	memset(&clients, 0, sizeof(struct client_cache_s));

	s = socket(PF_INET, SOCK_STREAM, 0);
	if (s < 0)
	{
		DPRINTF(E_ERROR, L_GENERAL, "socket(http): %s\n", strerror(errno));
		return -1;
	}

	if (setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &i, sizeof(i)) < 0)
		DPRINTF(E_WARN, L_GENERAL, "setsockopt(http, SO_REUSEADDR): %s\n", strerror(errno));

	memset(&listenname, 0, sizeof(struct sockaddr_in));
	listenname.sin_family = AF_INET;
	listenname.sin_port = htons(port);
	listenname.sin_addr.s_addr = htonl(INADDR_ANY);

	if (bind(s, (struct sockaddr *)&listenname, sizeof(struct sockaddr_in)) < 0)
	{
		DPRINTF(E_ERROR, L_GENERAL, "bind(http): %s\n", strerror(errno));
		close(s);
		return -1;
	}

	if (listen(s, 16) < 0)
	{
		DPRINTF(E_ERROR, L_GENERAL, "listen(http): %s\n", strerror(errno));
		close(s);
		return -1;
	}

	return s;
}

/* ProcessListen() :
 * accept incoming HTTP connection. */
static void
ProcessListen(struct event *ev)
{
	int shttp;
	socklen_t clientnamelen;
	struct sockaddr_in clientname;
	clientnamelen = sizeof(struct sockaddr_in);

	shttp = accept(ev->fd, (struct sockaddr *)&clientname, &clientnamelen);
	if (shttp<0)
	{
		DPRINTF(E_ERROR, L_GENERAL, "accept(http): %s\n", strerror(errno));
	}
	else
	{
		struct upnphttp * tmp = 0;
		DPRINTF(E_DEBUG, L_GENERAL, "HTTP connection from %s:%d\n",
			inet_ntoa(clientname.sin_addr),
			ntohs(clientname.sin_port) );
		/*if (fcntl(shttp, F_SETFL, O_NONBLOCK) < 0) {
			DPRINTF(E_ERROR, L_GENERAL, "fcntl F_SETFL, O_NONBLOCK\n");
		}*/
		/* Create a new upnphttp object and add it to
		 * the active upnphttp object list */
		tmp = New_upnphttp(shttp);
		if (tmp)
		{
			tmp->clientaddr = clientname.sin_addr;
			LIST_INSERT_HEAD(&upnphttphead, tmp, entries);
		}
		else
		{
			DPRINTF(E_ERROR, L_GENERAL, "New_upnphttp() failed\n");
			close(shttp);
		}
	}
}

/* Handler for the SIGTERM signal (kill) 
 * SIGINT is also handled */
static void
sigterm(int sig)
{
	signal(sig, SIG_IGN);	/* Ignore this signal while we are quitting */

	DPRINTF(E_WARN, L_GENERAL, "received signal %d, good-bye\n", sig);

	quitting = 1;
}

static void
sigusr1(int sig)
{
	signal(sig, sigusr1);
	DPRINTF(E_WARN, L_GENERAL, "received signal %d, clear cache\n", sig);

	memset(&clients, '\0', sizeof(clients));
}

static void
sighup(int sig)
{
	signal(sig, sighup);
	DPRINTF(E_WARN, L_GENERAL, "received signal %d, reloading\n", sig);

	reload_ifaces(1);
	log_reopen();
}

/* record the startup time */
static void
set_startup_time(void)
{
	startup_time = time(NULL);
}

static void
getfriendlyname(char *buf, int len)
{
	char *p = NULL;
	char hn[63];
	int off;

	if (gethostname(hn, sizeof(hn)) == 0)
	{
		strncpyt(buf, hn, len);
		p = strchr(buf, '.');
		if (p)
			*p = '\0';
	}
	else
		strcpy(buf, "Unknown");

	off = strlen(buf);
	off += snprintf(buf+off, len-off, ": ");
#ifdef READYNAS
	FILE *info;
	char ibuf[64], *key, *val;
	snprintf(buf+off, len-off, "ReadyNAS");
	info = fopen("/proc/sys/dev/boot/info", "r");
	if (!info)
		return;
	while ((val = fgets(ibuf, 64, info)) != NULL)
	{
		key = strsep(&val, ": \t");
		val = trim(val);
		if (strcmp(key, "model") == 0)
		{
			snprintf(buf+off, len-off, "%s", val);
			key = strchr(val, ' ');
			if (key)
			{
				strncpyt(modelnumber, key+1, MODELNUMBER_MAX_LEN);
				*key = '\0';
			}
			snprintf(modelname, MODELNAME_MAX_LEN,
				"Windows Media Connect compatible (%s)", val);
		}
		else if (strcmp(key, "serial") == 0)
		{
			strncpyt(serialnumber, val, SERIALNUMBER_MAX_LEN);
			if (serialnumber[0] == '\0')
			{
				char mac_str[13];
				if (getsyshwaddr(mac_str, sizeof(mac_str)) == 0)
					strcpy(serialnumber, mac_str);
				else
					strcpy(serialnumber, "0");
			}
			break;
		}
	}
	fclose(info);
#else
	char * logname;
	logname = getenv("USER");
	if (!logname)
        {
		logname = getenv("LOGNAME");
#ifndef STATIC // Disable for static linking
		if (!logname)
		{
			struct passwd *pwent = getpwuid(geteuid());
			if (pwent)
				logname = pwent->pw_name;
		}
#endif
	}
	snprintf(buf+off, len-off, "%s", logname?logname:"Unknown");
#endif
}

static time_t
_get_dbtime(void)
{
	char path[PATH_MAX];
	struct stat st;

	snprintf(path, sizeof(path), "%s/files.db", db_path);
	if (stat(path, &st) != 0)
		return 0;
	return st.st_mtime;
}

static int
open_db(sqlite3 **sq3)
{
	char path[PATH_MAX];
	int new_db = 0;

	snprintf(path, sizeof(path), "%s/files.db", db_path);
	if (access(path, F_OK) != 0)
	{
		new_db = 1;
		make_dir(db_path, S_ISVTX|S_IRWXU|S_IRWXG|S_IRWXO);
	}
	if (sqlite3_open(path, &db) != SQLITE_OK)
		DPRINTF(E_FATAL, L_GENERAL, "ERROR: Failed to open sqlite database!  Exiting...\n");
	if (sq3)
		*sq3 = db;
	sqlite3_busy_timeout(db, 5000);
	sql_exec(db, "pragma page_size = 4096");
	sql_exec(db, "pragma journal_mode = OFF");
	sql_exec(db, "pragma synchronous = OFF;");
	sql_exec(db, "pragma default_cache_size = 8192;");

	return new_db;
}

static void
check_db(sqlite3 *db, int new_db, pid_t *scanner_pid)
{
	struct media_dir_s *media_path = NULL;
	char cmd[PATH_MAX*2];
	char **result;
	int i, rows = 0;
	int ret;

	if (!new_db)
	{
		/* Check if any new media dirs appeared */
		media_path = media_dirs;
		while (media_path)
		{
			ret = sql_get_int_field(db, "SELECT TIMESTAMP as TYPE from DETAILS where PATH = %Q",
						media_path->path);
			if (ret != media_path->types)
			{
				ret = 1;
				goto rescan;
			}
			media_path = media_path->next;
		}
		/* Check if any media dirs disappeared */
		sql_get_table(db, "SELECT VALUE from SETTINGS where KEY = 'media_dir'", &result, &rows, NULL);
		for (i=1; i <= rows; i++)
		{
			media_path = media_dirs;
			while (media_path)
			{
				if (strcmp(result[i], media_path->path) == 0)
					break;
				media_path = media_path->next;
			}
			if (!media_path)
			{
				ret = 2;
				sqlite3_free_table(result);
				goto rescan;
			}
		}
		sqlite3_free_table(result);
	}

	ret = db_upgrade(db);
	if (ret != 0)
	{
rescan:
		CLEARFLAG(RESCAN_MASK);
		if (ret < 0)
			DPRINTF(E_WARN, L_GENERAL, "Creating new database at %s/files.db\n", db_path);
		else if (ret == 1)
			DPRINTF(E_WARN, L_GENERAL, "New media_dir detected; rebuilding...\n");
		else if (ret == 2)
			DPRINTF(E_WARN, L_GENERAL, "Removed media_dir detected; rebuilding...\n");
		else
			DPRINTF(E_WARN, L_GENERAL, "Database version mismatch (%d => %d); need to recreate...\n",
				ret, DB_VERSION);
		sqlite3_close(db);

		snprintf(cmd, sizeof(cmd), "rm -rf %s/files.db %s/art_cache", db_path, db_path);
		if (system(cmd) != 0)
			DPRINTF(E_FATAL, L_GENERAL, "Failed to clean old file cache!  Exiting...\n");

		open_db(&db);
		if (CreateDatabase() != 0)
			DPRINTF(E_FATAL, L_GENERAL, "ERROR: Failed to create sqlite database!  Exiting...\n");
	}
	if (ret || GETFLAG(RESCAN_MASK))
	{
#if USE_FORK
		sqlite3_close(db);
		*scanner_pid = fork();
		open_db(&db);
		if (*scanner_pid == 0) /* child (scanner) process */
		{
			start_scanner();
			sqlite3_close(db);
			log_close();
			freeoptions();
			free(children);
			exit(EXIT_SUCCESS);
		}
		else if (*scanner_pid < 0)
		{
			start_scanner();
		}
		else
			SETFLAG(SCANNING_MASK);
#else
		start_scanner();
#endif
	}
}

static int
writepidfile(const char *fname, int pid, uid_t uid)
{
	FILE *pidfile;
	struct stat st;
	char path[PATH_MAX], *dir;
	int ret = 0;

	if(!fname || *fname == '\0')
		return -1;

	/* Create parent directory if it doesn't already exist */
	strncpyt(path, fname, sizeof(path));
	dir = dirname(path);
	if (stat(dir, &st) == 0)
	{
		if (!S_ISDIR(st.st_mode))
		{
			DPRINTF(E_ERROR, L_GENERAL, "Pidfile path is not a directory: %s\n",
				fname);
			return -1;
		}
	}
	else
	{
		if (make_dir(dir, S_IRWXU|S_IRGRP|S_IXGRP|S_IROTH|S_IXOTH) != 0)
		{
			DPRINTF(E_ERROR, L_GENERAL, "Unable to create pidfile directory: %s\n",
				fname);
			return -1;
		}
		if (uid > 0)
		{
			if (chown(dir, uid, -1) != 0)
				DPRINTF(E_WARN, L_GENERAL, "Unable to change pidfile %s ownership: %s\n",
					dir, strerror(errno));
		}
	}
	
	pidfile = fopen(fname, "w");
	if (!pidfile)
	{
		DPRINTF(E_ERROR, L_GENERAL, "Unable to open pidfile for writing %s: %s\n",
			fname, strerror(errno));
		return -1;
	}

	if (fprintf(pidfile, "%d\n", pid) <= 0)
	{
		DPRINTF(E_ERROR, L_GENERAL, 
			"Unable to write to pidfile %s: %s\n", fname, strerror(errno));
		ret = -1;
	}
	if (uid > 0)
	{
		if (fchown(fileno(pidfile), uid, -1) != 0)
			DPRINTF(E_WARN, L_GENERAL, "Unable to change pidfile %s ownership: %s\n",
				fname, strerror(errno));
	}

	fclose(pidfile);

	return ret;
}

static int strtobool(const char *str)
{
	return ((strcasecmp(str, "yes") == 0) ||
		(strcasecmp(str, "true") == 0) ||
		(atoi(str) == 1));
}

static void init_nls(void)
{
#ifdef ENABLE_NLS
	const char *messages, *ctype, *locale_dir;

	ctype = setlocale(LC_CTYPE, "");
	if (!ctype || !strcmp(ctype, "C"))
		ctype = setlocale(LC_CTYPE, "en_US.utf8");
	if (!ctype)
		DPRINTF(E_WARN, L_GENERAL, "Unset locale\n");
	else if (!strstr(ctype, "utf8") && !strstr(ctype, "UTF8") &&
		 !strstr(ctype, "utf-8") && !strstr(ctype, "UTF-8"))
		DPRINTF(E_WARN, L_GENERAL, "Using unsupported non-utf8 locale '%s'\n", ctype);
	messages = setlocale(LC_MESSAGES, "");
	if (!messages)
		messages = "unset";
	locale_dir = bindtextdomain("minidlna", getenv("TEXTDOMAINDIR"));
	DPRINTF(E_DEBUG, L_GENERAL, "Using locale dir '%s' and locale langauge %s/%s\n", locale_dir, messages, ctype);
	textdomain("minidlna");
#endif
}

/* init phase :
 * 1) read configuration file
 * 2) read command line arguments
 * 3) daemonize
 * 4) check and write pid file
 * 5) set startup time stamp
 * 6) compute presentation URL
 * 7) set signal handlers */
static int
init(int argc, char **argv)
{
	int i;
	int pid;
	int debug_flag = 0;
	int verbose_flag = 0;
	int options_flag = 0;
	struct sigaction sa;
	const char * presurl = NULL;
	const char * optionsfile = "/etc/minidlna.conf";
	char mac_str[13];
	char *string, *word;
	char *path;
	char buf[PATH_MAX];
	char log_str[75] = "general,artwork,database,inotify,scanner,metadata,http,ssdp,tivo=warn";
	char *log_level = NULL;
	struct media_dir_s *media_dir;
	int ifaces = 0;
	media_types types;
	uid_t uid = 0;
	gid_t gid = 0;
	int error;

	/* first check if "-f" option is used */
	for (i=2; i<argc; i++)
	{
		if (strcmp(argv[i-1], "-f") == 0)
		{
			optionsfile = argv[i];
			options_flag = 1;
			break;
		}
	}

	/* set up uuid based on mac address */
	if (getsyshwaddr(mac_str, sizeof(mac_str)) < 0)
	{
		DPRINTF(E_OFF, L_GENERAL, "No MAC address found.  Falling back to generic UUID.\n");
		strcpy(mac_str, "554e4b4e4f57");
	}
	snprintf(uuidvalue+5, UUIDVALUE_MAX_LEN-5, "4d696e69-444c-164e-9d41-%s", mac_str);

	getfriendlyname(friendly_name, FRIENDLYNAME_MAX_LEN);
	
	runtime_vars.port = 8200;
	runtime_vars.notify_interval = 895;	/* seconds between SSDP announces */
	runtime_vars.max_connections = 50;
	runtime_vars.root_container = NULL;
	runtime_vars.ifaces[0] = NULL;

	/* read options file first since
	 * command line arguments have final say */
	if (readoptionsfile(optionsfile) < 0)
	{
		/* only error if file exists or using -f */
		if(access(optionsfile, F_OK) == 0 || options_flag)
			DPRINTF(E_FATAL, L_GENERAL, "Error reading configuration file %s\n", optionsfile);
	}

	for (i=0; i<num_options; i++)
	{
        DPRINTF(E_WARN, L_GENERAL, "Option #%d => %s\n", ary_options[i].id, ary_options[i].value);
		switch (ary_options[i].id)
		{
		case UPNPIFNAME:
			for (string = ary_options[i].value; (word = strtok(string, ",")); string = NULL)
			{
				if (ifaces >= MAX_LAN_ADDR)
				{
					DPRINTF(E_ERROR, L_GENERAL, "Too many interfaces (max: %d), ignoring %s\n",
						MAX_LAN_ADDR, word);
					break;
				}
				while (isspace(*word))
					word++;
				runtime_vars.ifaces[ifaces++] = word;
			}
			break;
		case UPNPPORT:
			runtime_vars.port = atoi(ary_options[i].value);
			break;
		case UPNPPRESENTATIONURL:
			presurl = ary_options[i].value;
			break;
		case UPNPNOTIFY_INTERVAL:
			runtime_vars.notify_interval = atoi(ary_options[i].value);
			break;
		case UPNPSERIAL:
			strncpyt(serialnumber, ary_options[i].value, SERIALNUMBER_MAX_LEN);
			break;				
		case UPNPMODEL_NAME:
			strncpyt(modelname, ary_options[i].value, MODELNAME_MAX_LEN);
			break;
		case UPNPMODEL_NUMBER:
			strncpyt(modelnumber, ary_options[i].value, MODELNUMBER_MAX_LEN);
			break;
		case UPNPFRIENDLYNAME:
			strncpyt(friendly_name, ary_options[i].value, FRIENDLYNAME_MAX_LEN);
			break;
		case UPNPMEDIADIR:
			types = ALL_MEDIA;
			path = ary_options[i].value;
			word = strchr(path, ',');
			if (word && (access(path, F_OK) != 0))
			{
				types = 0;
				while (*path)
				{
					if (*path == ',')
					{
						path++;
						break;
					}
					else if (*path == 'A' || *path == 'a')
						types |= TYPE_AUDIO;
					else if (*path == 'V' || *path == 'v')
						types |= TYPE_VIDEO;
					else if (*path == 'P' || *path == 'p')
						types |= TYPE_IMAGE;
					else
						DPRINTF(E_FATAL, L_GENERAL, "Media directory entry not understood [%s]\n",
							ary_options[i].value);
					path++;
				}
			}
			path = realpath(path, buf);
			if (!path || access(path, F_OK) != 0)
			{
				DPRINTF(E_ERROR, L_GENERAL, "Media directory \"%s\" not accessible [%s]\n",
					ary_options[i].value, strerror(errno));
				break;
			}
			media_dir = calloc(1, sizeof(struct media_dir_s));
			media_dir->path = strdup(path);
			media_dir->types = types;
			if (media_dirs)
			{
				struct media_dir_s *all_dirs = media_dirs;
				while( all_dirs->next )
					all_dirs = all_dirs->next;
				all_dirs->next = media_dir;
			}
			else
				media_dirs = media_dir;
			break;
		case UPNPALBUMART_NAMES:
			for (string = ary_options[i].value; (word = strtok(string, "/")); string = NULL)
			{
				struct album_art_name_s * this_name = calloc(1, sizeof(struct album_art_name_s));
				int len = strlen(word);
				if (word[len-1] == '*')
				{
					word[len-1] = '\0';
					this_name->wildcard = 1;
				}
				this_name->name = strdup(word);
				if (album_art_names)
				{
					struct album_art_name_s * all_names = album_art_names;
					while( all_names->next )
						all_names = all_names->next;
					all_names->next = this_name;
				}
				else
					album_art_names = this_name;
			}
			break;
		case UPNPDBDIR:
			path = realpath(ary_options[i].value, buf);
			if (!path)
				path = (ary_options[i].value);
			make_dir(path, S_ISVTX|S_IRWXU|S_IRWXG|S_IRWXO);
			if (access(path, F_OK) != 0)
				DPRINTF(E_FATAL, L_GENERAL, "Database path not accessible! [%s]\n", path);
			strncpyt(db_path, path, sizeof(db_path));
			break;
		case UPNPLOGDIR:
			path = realpath(ary_options[i].value, buf);
			if (!path)
				path = ary_options[i].value;
			if (snprintf(log_path, sizeof(log_path), "%s", path) > sizeof(log_path))
				DPRINTF(E_FATAL, L_GENERAL, "Log path too long! [%s]\n", path);
			make_dir(log_path, S_ISVTX|S_IRWXU|S_IRWXG|S_IRWXO);
			break;
		case UPNPLOGLEVEL:
			log_level = ary_options[i].value;
			break;
		case UPNPINOTIFY:
			if (!strtobool(ary_options[i].value))
				CLEARFLAG(INOTIFY_MASK);
			break;
		case ENABLE_TIVO:
			if (strtobool(ary_options[i].value))
				SETFLAG(TIVO_MASK);
			break;
		case ENABLE_DLNA_STRICT:
			if (strtobool(ary_options[i].value))
				SETFLAG(DLNA_STRICT_MASK);
			break;
		case ROOT_CONTAINER:
			switch (ary_options[i].value[0]) {
			case '.':
				runtime_vars.root_container = NULL;
				break;
			case 'B':
			case 'b':
				runtime_vars.root_container = BROWSEDIR_ID;
				break;
			case 'M':
			case 'm':
				runtime_vars.root_container = MUSIC_ID;
				break;
			case 'V':
			case 'v':
				runtime_vars.root_container = VIDEO_ID;
				break;
			case 'P':
			case 'p':
				runtime_vars.root_container = IMAGE_ID;
				break;
			default:
				runtime_vars.root_container = ary_options[i].value;
				DPRINTF(E_WARN, L_GENERAL, "Using arbitrary root container [%s]\n",
					ary_options[i].value);
				break;
			}
			break;
		case UPNPMINISSDPDSOCKET:
			minissdpdsocketpath = ary_options[i].value;
			break;
		case UPNPUUID:
			strcpy(uuidvalue+5, ary_options[i].value);
			break;
		case USER_ACCOUNT:
			uid = strtoul(ary_options[i].value, &string, 0);
			if (*string)
			{
				/* Symbolic username given, not UID. */
				struct passwd *entry = getpwnam(ary_options[i].value);
				if (!entry)
					DPRINTF(E_FATAL, L_GENERAL, "Bad user '%s'.\n",
						ary_options[i].value);
				uid = entry->pw_uid;
				if (!gid)
					gid = entry->pw_gid;
			}
			break;
		case FORCE_SORT_CRITERIA:
			force_sort_criteria = ary_options[i].value;
			if (force_sort_criteria[0] == '!')
			{
				SETFLAG(FORCE_ALPHASORT_MASK);
				force_sort_criteria++;
			}
			break;
		case MAX_CONNECTIONS:
			runtime_vars.max_connections = atoi(ary_options[i].value);
			break;
		case MERGE_MEDIA_DIRS:
			if (strtobool(ary_options[i].value))
				SETFLAG(MERGE_MEDIA_DIRS_MASK);
			break;
		case WIDE_LINKS:
			if (strtobool(ary_options[i].value))
				SETFLAG(WIDE_LINKS_MASK);
			break;
		case TIVO_DISCOVERY:
			if (strcasecmp(ary_options[i].value, "beacon") == 0)
				CLEARFLAG(TIVO_BONJOUR_MASK);
			break;
		case ENABLE_SUBTITLES:
			if (!strtobool(ary_options[i].value))
				CLEARFLAG(SUBTITLES_MASK);
			break;
		case ICON_SM_PNG:
            icon_sm_png = file_get_content(ary_options[i].value);
			break;
		case ICON_LRG_PNG:
            icon_lrg_png = file_get_content(ary_options[i].value);
			break;
		case ICON_SM_JPG:
            icon_sm_jpg = file_get_content(ary_options[i].value);
			break;
		case ICON_LRG_JPG:
            icon_lrg_jpg = file_get_content(ary_options[i].value);
			break;
		default:
			DPRINTF(E_ERROR, L_GENERAL, "Unknown option in file %s\n",
				optionsfile);
		}
	}
	if (!log_path[0])
		strncpyt(log_path, DEFAULT_LOG_PATH, sizeof(log_path));
	if (!db_path[0])
		strncpyt(db_path, DEFAULT_DB_PATH, sizeof(db_path));

	/* command line arguments processing */
	for (i=1; i<argc; i++)
	{
		if (argv[i][0] != '-')
		{
			DPRINTF(E_FATAL, L_GENERAL, "Unknown option: %s\n", argv[i]);
		}
		else if (strcmp(argv[i], "--help") == 0)
		{
			runtime_vars.port = -1;
			break;
		}
		else switch(argv[i][1])
		{
		case 't':
			if (i+1 < argc)
				runtime_vars.notify_interval = atoi(argv[++i]);
			else
				DPRINTF(E_FATAL, L_GENERAL, "Option -%c takes one argument.\n", argv[i][1]);
			break;
		case 's':
			if (i+1 < argc)
				strncpyt(serialnumber, argv[++i], SERIALNUMBER_MAX_LEN);
			else
				DPRINTF(E_FATAL, L_GENERAL, "Option -%c takes one argument.\n", argv[i][1]);
			break;
		case 'm':
			if (i+1 < argc)
				strncpyt(modelnumber, argv[++i], MODELNUMBER_MAX_LEN);
			else
				DPRINTF(E_FATAL, L_GENERAL, "Option -%c takes one argument.\n", argv[i][1]);
			break;
		case 'p':
			if (i+1 < argc)
				runtime_vars.port = atoi(argv[++i]);
			else
				DPRINTF(E_FATAL, L_GENERAL, "Option -%c takes one argument.\n", argv[i][1]);
			break;
		case 'P':
			if (i+1 < argc)
			{
				if (argv[++i][0] != '/')
					DPRINTF(E_FATAL, L_GENERAL, "Option -%c requires an absolute filename.\n", argv[i-1][1]);
				else
					pidfilename = argv[i];
			}
			else
				DPRINTF(E_FATAL, L_GENERAL, "Option -%c takes one argument.\n", argv[i][1]);
			break;
		case 'd':
			debug_flag = 1;
		case 'v':
			verbose_flag = 1;
			break;
		case 'L':
			SETFLAG(NO_PLAYLIST_MASK);
			break;
		case 'w':
			if (i+1 < argc)
				presurl = argv[++i];
			else
				DPRINTF(E_FATAL, L_GENERAL, "Option -%c takes one argument.\n", argv[i][1]);
			break;
		case 'i':
			if (i+1 < argc)
			{
				i++;
				if (ifaces >= MAX_LAN_ADDR)
				{
					DPRINTF(E_ERROR, L_GENERAL, "Too many interfaces (max: %d), ignoring %s\n",
						MAX_LAN_ADDR, argv[i]);
					break;
				}
				runtime_vars.ifaces[ifaces++] = argv[i];
			}
			else
				DPRINTF(E_FATAL, L_GENERAL, "Option -%c takes one argument.\n", argv[i][1]);
			break;
		case 'f':
			i++;	/* discarding, the config file is already read */
			break;
		case 'h':
			runtime_vars.port = -1; // triggers help display
			break;
		case 'r':
			SETFLAG(RESCAN_MASK);
			break;
		case 'R':
			snprintf(buf, sizeof(buf), "rm -rf %s/files.db %s/art_cache", db_path, db_path);
			if (system(buf) != 0)
				DPRINTF(E_FATAL, L_GENERAL, "Failed to clean old file cache %s. EXITING\n", db_path);
			break;
		case 'u':
			if (i+1 != argc)
			{
				i++;
				uid = strtoul(argv[i], &string, 0);
				if (*string)
				{
					/* Symbolic username given, not UID. */
					struct passwd *entry = getpwnam(argv[i]);
					if (!entry)
						DPRINTF(E_FATAL, L_GENERAL, "Bad user '%s'.\n", argv[i]);
					uid = entry->pw_uid;
					if (!gid)
						gid = entry->pw_gid;
				}
			}
			else
				DPRINTF(E_FATAL, L_GENERAL, "Option -%c takes one argument.\n", argv[i][1]);
			break;
		case 'g':
			if (i+1 != argc)
			{
				i++;
				gid = strtoul(argv[i], &string, 0);
				if (*string)
				{
					/* Symbolic group given, not GID. */
					struct group *grp = getgrnam(argv[i]);
					if (!grp)
						DPRINTF(E_FATAL, L_GENERAL, "Bad group '%s'.\n", argv[i]);
					gid = grp->gr_gid;
				}
			}
			else
				DPRINTF(E_FATAL, L_GENERAL, "Option -%c takes one argument.\n", argv[i][1]);
			break;
#if defined(__linux__) || defined(__APPLE__)
		case 'S':
			SETFLAG(SYSTEMD_MASK);
			break;
#endif
		case 'V':
			printf("Version " MINIDLNA_VERSION "\n");
			exit(0);
			break;
		default:
			DPRINTF(E_ERROR, L_GENERAL, "Unknown option: %s\n", argv[i]);
			runtime_vars.port = -1; // triggers help display
		}
	}

	if (runtime_vars.port <= 0)
	{
		printf("Usage:\n\t"
			"%s [-d] [-v] [-f config_file] [-p port]\n"
			"\t\t[-i network_interface] [-u uid_to_run_as] [-g group_to_run_as]\n"
			"\t\t[-t notify_interval] [-P pid_filename]\n"
			"\t\t[-s serial] [-m model_number]\n"
#ifdef __linux__
			"\t\t[-w url] [-r] [-R] [-L] [-S] [-V] [-h]\n"
#else
			"\t\t[-w url] [-r] [-R] [-L] [-V] [-h]\n"
#endif
			"\nNotes:\n\tNotify interval is in seconds. Default is 895 seconds.\n"
			"\tDefault pid file is %s.\n"
			"\tWith -d minidlna will run in debug mode (not daemonize).\n"
			"\t-w sets the presentation url. Default is http address on port 80\n"
			"\t-v enables verbose output\n"
			"\t-h displays this text\n"
			"\t-r forces a rescan\n"
			"\t-R forces a rebuild\n"
			"\t-L do not create playlists\n"
#if defined(__linux__) || defined(__APPLE__)
			"\t-S changes behaviour for systemd/launchd\n"
#endif
			"\t-V print the version number\n",
			argv[0], pidfilename);
		return 1;
	}

	if (verbose_flag)
	{
		strcpy(log_str+65, "debug");
		log_level = log_str;
	}
	else if (!log_level)
		log_level = log_str;

	/* Set the default log to stdout */
	if (debug_flag)
	{
		pid = getpid();
		strcpy(log_str+65, "maxdebug");
		log_level = log_str;
		log_path[0] = '\0';
	}
	else if (GETFLAG(SYSTEMD_MASK))
	{
		pid = getpid();
		log_path[0] = '\0';
	}
	else
	{
		pid = process_daemonize();
		if (access(db_path, F_OK) != 0)
			make_dir(db_path, S_ISVTX|S_IRWXU|S_IRWXG|S_IRWXO);
	}
	if (log_init(log_level) < 0)
		DPRINTF(E_FATAL, L_GENERAL, "Failed to open log file '%s/" LOGFILE_NAME "': %s\n",
			log_path, strerror(errno));

	if (process_check_if_running(pidfilename) < 0)
		DPRINTF(E_FATAL, L_GENERAL, SERVER_NAME " is already running. EXITING.\n");

	set_startup_time();

	/* presentation url */
	if (presurl)
		strncpyt(presentationurl, presurl, PRESENTATIONURL_MAX_LEN);
	else
		strcpy(presentationurl, "/");

	/* set signal handlers */
	memset(&sa, 0, sizeof(struct sigaction));
	sa.sa_handler = sigterm;
	if (sigaction(SIGTERM, &sa, NULL))
		DPRINTF(E_FATAL, L_GENERAL, "Failed to set %s handler. EXITING.\n", "SIGTERM");
	if (sigaction(SIGINT, &sa, NULL))
		DPRINTF(E_FATAL, L_GENERAL, "Failed to set %s handler. EXITING.\n", "SIGINT");
	if (signal(SIGPIPE, SIG_IGN) == SIG_ERR)
		DPRINTF(E_FATAL, L_GENERAL, "Failed to set %s handler. EXITING.\n", "SIGPIPE");
	if (signal(SIGHUP, &sighup) == SIG_ERR)
		DPRINTF(E_FATAL, L_GENERAL, "Failed to set %s handler. EXITING.\n", "SIGHUP");
	if (signal(SIGUSR2, SIG_IGN) == SIG_ERR)
		DPRINTF(E_FATAL, L_GENERAL, "Failed to set %s handler. EXITING.\n", "SIGUSR2");
	signal(SIGUSR1, &sigusr1);
	sa.sa_handler = process_handle_child_termination;
	if (sigaction(SIGCHLD, &sa, NULL))
		DPRINTF(E_FATAL, L_GENERAL, "Failed to set %s handler. EXITING.\n", "SIGCHLD");

	if (writepidfile(pidfilename, pid, uid) != 0)
		pidfilename = NULL;

	if (uid > 0)
	{
		struct stat st;
		if (stat(db_path, &st) == 0 && st.st_uid != uid && chown(db_path, uid, -1) != 0)
			DPRINTF(E_ERROR, L_GENERAL, "Unable to set db_path [%s] ownership to %d: %s\n",
				db_path, uid, strerror(errno));
	}

	if (gid > 0 && setgid(gid) == -1)
		DPRINTF(E_FATAL, L_GENERAL, "Failed to switch to gid '%d'. [%s] EXITING.\n",
			gid, strerror(errno));

	if (uid > 0 && setuid(uid) == -1)
		DPRINTF(E_FATAL, L_GENERAL, "Failed to switch to uid '%d'. [%s] EXITING.\n",
			uid, strerror(errno));

	children = calloc(runtime_vars.max_connections, sizeof(struct child));
	if (!children)
	{
		DPRINTF(E_ERROR, L_GENERAL, "Allocation failed\n");
		return 1;
	}

	if ((error = event_module.init()) != 0)
		DPRINTF(E_FATAL, L_GENERAL, "Failed to init event module. "
		    "[%s] EXITING.\n", strerror(error));

	return 0;
}

/* === main === */
/* process HTTP or SSDP requests */
int
main(int argc, char **argv)
{
	int ret, i;
	int shttpl = -1;
	int smonitor = -1;
	struct upnphttp * e = 0;
	struct upnphttp * next;
	struct timeval tv, timeofday, lastnotifytime = {0, 0};
	time_t lastupdatetime = 0, lastdbtime = 0;
	u_long timeout;	/* in milliseconds */
	int last_changecnt = 0;
	pid_t scanner_pid = 0;
	pthread_t inotify_thread = 0;
	struct event ssdpev, httpev, monev;
#ifdef TIVO_SUPPORT
	uint8_t beacon_interval = 5;
	int sbeacon = -1;
	struct sockaddr_in tivo_bcast;
	struct timeval lastbeacontime = {0, 0};
	struct event beaconev;
#endif

	for (i = 0; i < L_MAX; i++)
		log_level[i] = E_WARN;

	ret = init(argc, argv);
	if (ret != 0)
		return 1;
	init_nls();

	DPRINTF(E_WARN, L_GENERAL, "Starting " SERVER_NAME " version " MINIDLNA_VERSION ".\n");

	if (sqlite3_libversion_number() < 3005001)
	{
		DPRINTF(E_WARN, L_GENERAL, "SQLite library is old.  Please use version 3.5.1 or newer.\n");
	}

	LIST_INIT(&upnphttphead);

	ret = open_db(NULL);
	if (ret == 0)
	{
		updateID = sql_get_int_field(db, "SELECT VALUE from SETTINGS where KEY = 'UPDATE_ID'");
		if (updateID == -1)
			ret = -1;
	}
	check_db(db, ret, &scanner_pid);
	lastdbtime = _get_dbtime();
#ifdef HAVE_INOTIFY
	if( GETFLAG(INOTIFY_MASK) )
	{
		if (!sqlite3_threadsafe() || sqlite3_libversion_number() < 3005001)
			DPRINTF(E_ERROR, L_GENERAL, "SQLite library is not threadsafe!  "
			                            "Inotify will be disabled.\n");
		else if (pthread_create(&inotify_thread, NULL, start_inotify, NULL) != 0)
			DPRINTF(E_FATAL, L_GENERAL, "ERROR: pthread_create() failed for start_inotify. EXITING\n");
	}
#endif /* HAVE_INOTIFY */

#ifdef HAVE_KQUEUE
	if (!GETFLAG(SCANNING_MASK)) {
		lav_register_all();
		kqueue_monitor_start();
	}
#endif /* HAVE_KQUEUE */

	smonitor = OpenAndConfMonitorSocket();
	if (smonitor > 0)
	{
		monev = (struct event ){ .fd = smonitor, .rdwr = EVENT_READ, .process = ProcessMonitorEvent };
		event_module.add(&monev);
	}

	sssdp = OpenAndConfSSDPReceiveSocket();
	if (sssdp < 0)
	{
		DPRINTF(E_INFO, L_GENERAL, "Failed to open socket for receiving SSDP. Trying to use MiniSSDPd\n");
		reload_ifaces(0);	/* populate lan_addr[0].str */
		if (SubmitServicesToMiniSSDPD(lan_addr[0].str, runtime_vars.port) < 0)
			DPRINTF(E_FATAL, L_GENERAL, "Failed to connect to MiniSSDPd. EXITING");
	}
	else
	{
		ssdpev = (struct event ){ .fd = sssdp, .rdwr = EVENT_READ, .process = ProcessSSDPRequest };
		event_module.add(&ssdpev);
	}

	/* open socket for HTTP connections. */
	shttpl = OpenAndConfHTTPSocket(runtime_vars.port);
	if (shttpl < 0)
		DPRINTF(E_FATAL, L_GENERAL, "Failed to open socket for HTTP. EXITING\n");
	DPRINTF(E_WARN, L_GENERAL, "HTTP listening on port %d\n", runtime_vars.port);
	httpev = (struct event ){ .fd = shttpl, .rdwr = EVENT_READ, .process = ProcessListen };
	event_module.add(&httpev);

#ifdef TIVO_SUPPORT
	if (GETFLAG(TIVO_MASK))
	{
		DPRINTF(E_WARN, L_GENERAL, "TiVo support is enabled.\n");
		/* Add TiVo-specific randomize function to sqlite */
		ret = sqlite3_create_function(db, "tivorandom", 1, SQLITE_UTF8, NULL, &TiVoRandomSeedFunc, NULL, NULL);
		if (ret != SQLITE_OK)
			DPRINTF(E_ERROR, L_TIVO, "ERROR: Failed to add sqlite randomize function for TiVo!\n");
		if (GETFLAG(TIVO_BONJOUR_MASK))
		{
			tivo_bonjour_register();
		}
		else
		{
			/* open socket for sending Tivo notifications */
			sbeacon = OpenAndConfTivoBeaconSocket();
			if(sbeacon < 0)
				DPRINTF(E_FATAL, L_GENERAL, "Failed to open sockets for sending Tivo beacon notify "
					"messages. EXITING\n");
			beaconev = (struct event ){ .fd = sbeacon, .rdwr = EVENT_READ, .process = ProcessTiVoBeacon };
			event_module.add(&beaconev);
			tivo_bcast.sin_family = AF_INET;
			tivo_bcast.sin_addr.s_addr = htonl(getBcastAddress());
			tivo_bcast.sin_port = htons(2190);
		}
	}
#endif

	reload_ifaces(0);
	lastnotifytime.tv_sec = time(NULL) + runtime_vars.notify_interval;

	/* main loop */
	while (!quitting)
	{
		if (gettimeofday(&timeofday, 0) < 0)
			DPRINTF(E_FATAL, L_GENERAL, "gettimeofday(): %s\n", strerror(errno));
		/* Check if we need to send SSDP NOTIFY messages and do it if
		 * needed */
		tv = lastnotifytime;
		tv.tv_sec += runtime_vars.notify_interval;
		if (timevalcmp(&timeofday, &tv, >=))
		{
			DPRINTF(E_DEBUG, L_SSDP, "Sending SSDP notifies\n");
			for (i = 0; i < n_lan_addr; i++)
			{
				SendSSDPNotifies(lan_addr[i].snotify, lan_addr[i].str,
					runtime_vars.port, runtime_vars.notify_interval);
			}
			lastnotifytime = timeofday;
			timeout = runtime_vars.notify_interval * 1000;
		}
		else
		{
			timevalsub(&tv, &timeofday);
			timeout = tv.tv_sec * 1000 + tv.tv_usec / 1000;
		}
#ifdef TIVO_SUPPORT
		if (sbeacon >= 0)
		{
			u_long beacontimeout;

			tv = lastbeacontime;
			tv.tv_sec += beacon_interval;
			if (timevalcmp(&timeofday, &tv, >=))
			{
				sendBeaconMessage(sbeacon, &tivo_bcast, sizeof(struct sockaddr_in), 1);
				lastbeacontime = timeofday;
				beacontimeout = beacon_interval * 1000;
				if (timeout > beacon_interval * 1000)
					timeout = beacon_interval * 1000;
				/* Beacons should be sent every 5 seconds or
				 * so for the first minute, then every minute
				 * or so thereafter. */
				if (beacon_interval == 5 && (timeofday.tv_sec - startup_time) > 60)
					beacon_interval = 60;
			}
			else
			{
				timevalsub(&tv, &timeofday);
				beacontimeout = tv.tv_sec * 1000 +
				    tv.tv_usec / 1000;
			}
			if (timeout > beacontimeout)
				timeout = beacontimeout;
		}
#endif

		if (GETFLAG(SCANNING_MASK) && kill(scanner_pid, 0) != 0) {
			CLEARFLAG(SCANNING_MASK);
			if (_get_dbtime() != lastdbtime)
				updateID++;
#ifdef HAVE_KQUEUE
			lav_register_all();
			kqueue_monitor_start();
#endif /* HAVE_KQUEUE */
		}

		event_module.process(timeout);
		if (quitting)
			goto shutdown;

		upnpevents_gc();

		/* increment SystemUpdateID if the content database has changed,
		 * and if there is an active HTTP connection, at most once every 2 seconds */
		if (!LIST_EMPTY(&upnphttphead) &&
		    (timeofday.tv_sec >= (lastupdatetime + 2)))
		{
			if (GETFLAG(SCANNING_MASK))
			{
				time_t dbtime = _get_dbtime();
				if (dbtime != lastdbtime)
				{
					lastdbtime = dbtime;
					last_changecnt = -1;
				}
			}
			if (sqlite3_total_changes(db) != last_changecnt)
			{
				updateID++;
				last_changecnt = sqlite3_total_changes(db);
				upnp_event_var_change_notify(EContentDirectory);
				lastupdatetime = timeofday.tv_sec;
			}
		}
		/* delete finished HTTP connections */
		for (e = upnphttphead.lh_first; e != NULL; e = next)
		{
			next = e->entries.le_next;
			if(e->state >= 100)
			{
				LIST_REMOVE(e, entries);
				Delete_upnphttp(e);
			}
		}
	}

shutdown:
	/* kill the scanner */
	if (GETFLAG(SCANNING_MASK) && scanner_pid)
		kill(scanner_pid, SIGKILL);

	/* close out open sockets */
	while (upnphttphead.lh_first != NULL)
	{
		e = upnphttphead.lh_first;
		LIST_REMOVE(e, entries);
		Delete_upnphttp(e);
	}
	if (sssdp >= 0)
		close(sssdp);
	if (shttpl >= 0)
		close(shttpl);
#ifdef TIVO_SUPPORT
	if (sbeacon >= 0)
		close(sbeacon);
#endif
	if (smonitor >= 0)
		close(smonitor);
	
	for (i = 0; i < n_lan_addr; i++)
	{
		SendSSDPGoodbyes(lan_addr[i].snotify);
		close(lan_addr[i].snotify);
	}

	if (inotify_thread)
	{
		pthread_kill(inotify_thread, SIGCHLD);
		pthread_join(inotify_thread, NULL);
	}

	/* kill other child processes */
	process_reap_children();
	free(children);

	event_module.fini();

	sql_exec(db, "UPDATE SETTINGS set VALUE = '%u' where KEY = 'UPDATE_ID'", updateID);
	sqlite3_close(db);

	upnpevents_removeSubscribers();

	if (pidfilename && unlink(pidfilename) < 0)
		DPRINTF(E_ERROR, L_GENERAL, "Failed to remove pidfile %s: %s\n", pidfilename, strerror(errno));

	log_close();
	freeoptions();

	exit(EXIT_SUCCESS);
}

