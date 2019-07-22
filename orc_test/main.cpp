#include "llvm/ExecutionEngine/Orc/Core.h"
#include "llvm/ExecutionEngine/Orc/LLJIT.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"

#include "llvm/Bitcode/BitcodeReader.h"
#include <iostream>

#include "clang/Frontend/CompilerInstance.h"
#include "clang/CodeGen/CodeGenAction.h"

using namespace std::chrono;
using namespace llvm;
using namespace orc;


std::unique_ptr<MemoryBuffer> fromFile(const char* path) {
    llvm::ErrorOr<std::unique_ptr<MemoryBuffer>> MBOrErr = MemoryBuffer::getFile(path);

    if (!MBOrErr)  {
	printf("Could not open %s\n", path);
	exit(-1);
    }

    return std::move(MBOrErr.get());
}

std::unique_ptr<llvm::Module> getModule(LLVMContext* ctx, const char* path) {
    std::unique_ptr<MemoryBuffer> b = fromFile(path);

    Expected< std::unique_ptr< Module > > mr = parseBitcodeFile(b->getMemBufferRef(), *ctx);
    if (!mr) {
	printf("Loading module failed");
	exit(-1);
    }
    return std::move(*mr);
}

std::unique_ptr<llvm::Module>
compile(llvm::LLVMContext* ctx,
	const char *const * args,
	const char *const * argEnd) {


    IntrusiveRefCntPtr<clang::DiagnosticIDs > diags(new clang::DiagnosticIDs());
    IntrusiveRefCntPtr<clang::DiagnosticOptions > diagOpts(new clang::DiagnosticOptions());

    clang::DiagnosticsEngine diagEngine(diags, diagOpts);

    std::shared_ptr<clang::CompilerInvocation> invocation(new clang::CompilerInvocation());
    clang::CompilerInvocation::CreateFromArgs(*invocation, args, argEnd, diagEngine);

    // Create the compiler instance
    clang::CompilerInstance instance;
    instance.setInvocation(invocation);

    instance.createDiagnostics();
    if (!instance.hasDiagnostics()) {
	std::cerr << "Compiled diagnostics failed" << std::endl;
	exit(-1);
    }

    // Generate LLVM using the compiler.
    clang::EmitLLVMOnlyAction act(ctx);
    if (!instance.ExecuteAction(act)) {
	std::cerr << "Action failed!" << std::endl;
	exit(-1);
    }
    std::unique_ptr< llvm::Module > modPtr = act.takeModule();
    return std::move(modPtr);
}


std::unique_ptr<llvm::Module> compileC(llvm::LLVMContext* ctx, const char* path) {
    const char * args[] = { path };
    const char *const * argEnd = args + sizeof(args) / sizeof(args[0]);
    return compile(ctx, args, argEnd);
}

std::unique_ptr<llvm::Module> compileCPP(llvm::LLVMContext* ctx, const char* path) {
    const char * args[] = { path, "-stdlib=libc++" };
    const char *const * argEnd = args + sizeof(args) / sizeof(args[0]);
    return compile(ctx, args, argEnd);
}

typedef uint64_t (*add_fn)(uint64_t, uint64_t);

typedef uint64_t (*fib_fn)(uint64_t);

typedef std::unique_ptr<llvm::Module> (*moduleFn)(llvm::LLVMContext* ctx, const char* path);

DataLayout getProcessDataLayout(JITTargetMachineBuilder& jtmb) {

    auto TM = jtmb.createTargetMachine();
    if (!TM) {
	printf("!TM\n");
	Error e = TM.takeError();
	outs() << "Get datalayout error: " << e;
	exit(-1);
    }

    return DataLayout((*TM)->createDataLayout());
}

SymbolNameSet getFailedSymbols(const SymbolFlagsMap& SymbolFlags) {
    SymbolNameSet FailedSymbols;
    for (auto &KV : SymbolFlags)
	FailedSymbols.insert(KV.first);
    return FailedSymbols;
}

class MyJITDylib;
class MyMaterializationUnit;
class MyMaterializationResponsibility;

/// A base class for materialization failures that allows the failing
///        symbols to be obtained for logging.
using MySymbolDependenceMap = DenseMap<MyJITDylib *, SymbolNameSet>;

/// A symbol query that returns results via a callback when results are
///        ready.
///
/// makes a callback when all symbols are available.
class MyAsynchronousSymbolQuery {
public:

    /// Create a query for the given symbols, notify-resolved and
    ///        notify-ready callbacks.
    MyAsynchronousSymbolQuery(const SymbolNameSet &Symbols,
			      SymbolsResolvedCallback NotifySymbolsResolved,
			      SymbolsReadyCallback NotifySymbolsReady)
	: NotifySymbolsResolved(std::move(NotifySymbolsResolved)),
	  NotifySymbolsReady(std::move(NotifySymbolsReady)) {
	NotYetResolvedCount = NotYetReadyCount = Symbols.size();

	for (auto &S : Symbols)
	    ResolvedSymbols[S] = nullptr;
    }


    /// Set the resolved symbol information for the given symbol name.
    void resolve(const SymbolStringPtr &Name, JITEvaluatedSymbol Sym) {
	auto I = ResolvedSymbols.find(Name);
	assert(I != ResolvedSymbols.end() &&
	       "Resolving symbol outside the requested set");
	assert(I->second.getAddress() == 0 && "Redundantly resolving symbol Name");
	I->second = std::move(Sym);
	--NotYetResolvedCount;
    }

    /// Call the NotifySymbolsResolved callback.
    ///
    /// This should only be called if all symbols covered by the query have been
    /// resolved.
    void handleFullyResolved() {
	assert(NotYetResolvedCount == 0 && "Not fully resolved?");

	if (!NotifySymbolsResolved) {
	    // handleFullyResolved may be called by handleFullyReady (see comments in
	    // that method), in which case this is a no-op, so bail out.
	    assert(!NotifySymbolsReady &&
		   "NotifySymbolsResolved already called or an error occurred");
	    return;
	}

	auto TmpNotifySymbolsResolved = std::move(NotifySymbolsResolved);
	NotifySymbolsResolved = SymbolsResolvedCallback();
	TmpNotifySymbolsResolved(std::move(ResolvedSymbols));
    }

    /// Notify the query that a requested symbol is ready for execution.
    void notifySymbolReady() {
	assert(NotYetReadyCount != 0 && "All symbols already emitted");
	--NotYetReadyCount;
    }

    /// Returns true if all symbols covered by this query are ready.
    bool isFullyReady() const { return NotYetReadyCount == 0; }

    /// Calls the NotifySymbolsReady callback.
    ///
    /// This should only be called if all symbols covered by this query are ready.
    void handleFullyReady() {
	assert(NotifySymbolsReady &&
	       "NotifySymbolsReady already called or an error occurred");

	auto TmpNotifySymbolsReady = std::move(NotifySymbolsReady);
	NotifySymbolsReady = SymbolsReadyCallback();

	if (NotYetResolvedCount == 0 && NotifySymbolsResolved) {
	    // The NotifyResolved callback of one query must have caused this query to
	    // become ready (i.e. there is still a handleFullyResolved callback waiting
	    // to be made back up the stack). Fold the handleFullyResolved call into
	    // this one before proceeding. This will cause the call further up the
	    // stack to become a no-op.
	    handleFullyResolved();
	}

	assert(QueryRegistrations.empty() &&
	       "Query is still registered with some symbols");
	assert(!NotifySymbolsResolved && "Resolution not applied yet");
	TmpNotifySymbolsReady(Error::success());
    }

    void removeQueryDependence(MyJITDylib &JD, const SymbolStringPtr &Name) {
	auto QRI = QueryRegistrations.find(&JD);
	assert(QRI != QueryRegistrations.end() &&
	       "No dependencies registered for JD");
	assert(QRI->second.count(Name) && "No dependency on Name in JD");
	QRI->second.erase(Name);
	if (QRI->second.empty())
	    QueryRegistrations.erase(QRI);
    }

    void handleFailed(Error Err) {
	assert(QueryRegistrations.empty()
	       && ResolvedSymbols.empty()
	       && NotYetResolvedCount == 0
	       && NotYetReadyCount == 0
	       && "Query should already have been abandoned");
	if (NotifySymbolsResolved) {
	    NotifySymbolsResolved(std::move(Err));
	    NotifySymbolsResolved = SymbolsResolvedCallback();
	} else {
	    assert(NotifySymbolsReady && "Failed after both callbacks issued?");
	    NotifySymbolsReady(std::move(Err));
	}
	NotifySymbolsReady = SymbolsReadyCallback();
    }

private:
    SymbolsResolvedCallback NotifySymbolsResolved;
    SymbolsReadyCallback NotifySymbolsReady;
public:
    MySymbolDependenceMap QueryRegistrations;
private:
    SymbolMap ResolvedSymbols;
public:
    size_t NotYetResolvedCount;
    size_t NotYetReadyCount;
};


/// A MaterializationUnit represents a set of symbol definitions that can
///        be materialized as a group, or individually discarded (when
///        overriding definitions are encountered).
///
/// MaterializationUnits are used when providing lazy definitions of symbols to
/// JITDylibs. The JITDylib will call materialize when the address of a symbol
/// is requested via the lookup method. The JITDylib will call discard if a
/// stronger definition is added or already present.
class MyMaterializationUnit {
public:
    MyMaterializationUnit() {}

    virtual ~MyMaterializationUnit() {}

    /// Return the set of symbols that this source provides.
    virtual const SymbolFlagsMap& getSymbols() const = 0;

    /// Implementations of this method should materialize all symbols
    ///        in the materialzation unit, except for those that have been
    ///        previously discarded.
    virtual void materialize(MyJITDylib &JD) = 0;

    /// Called by JITDylibs to notify MaterializationUnits that the given symbol
    /// has been overridden.
    virtual void discard(const MyJITDylib &JD, const SymbolStringPtr &Name) = 0;
};

using MyMaterializationUnitList =
    std::vector<std::unique_ptr<MyMaterializationUnit>>;

/// A symbol table that supports asynchoronous symbol queries.
///
/// Represents a virtual shared object. Instances can not be copied or moved, so
/// their addresses may be used as keys for resource management.
/// JITDylib state changes must be made via an ExecutionSession to guarantee
/// that they are synchronized with respect to other JITDylib operations.
class MyJITDylib {
public:
    using GeneratorFunction = std::function<SymbolNameSet(MyJITDylib &Parent, const SymbolNameSet &Names)>;

    using AsynchronousSymbolQuerySet =
	std::set<std::shared_ptr<MyAsynchronousSymbolQuery>>;

    MyJITDylib() {}
    MyJITDylib(const MyJITDylib &) = delete;
    MyJITDylib &operator=(const MyJITDylib &) = delete;
    MyJITDylib(MyJITDylib &&) = delete;
    MyJITDylib &operator=(MyJITDylib &&) = delete;

  /// Tries to remove the given symbols.
  ///
  /// If any symbols are not defined in this JITDylib this method will return
  /// a SymbolsNotFound error covering the missing symbols.
  ///
  /// If all symbols are found but some symbols are in the process of being
  /// materialized this method will return a SymbolsCouldNotBeRemoved error.
  ///
  /// On success, all symbols are removed. On failure, the JITDylib state is
  /// left unmodified (no symbols are removed).
  Error remove(const SymbolNameSet &Names);

  /// Search the given JITDylib for the symbols in Symbols. If found, store
  ///        the flags for each symbol in Flags. Returns any unresolved symbols.
  SymbolFlagsMap lookupFlags(const SymbolNameSet &Names);

private:
  using AsynchronousSymbolQueryList =
      std::vector<std::shared_ptr<MyAsynchronousSymbolQuery>>;


public:
    struct MaterializingInfo {
	AsynchronousSymbolQueryList PendingQueries;
	MySymbolDependenceMap Dependants;
	MySymbolDependenceMap UnemittedDependencies;
	bool IsEmitted = false;
    };
    void transferEmittedNodeDependencies(MaterializingInfo &DependantMI,
					 const SymbolStringPtr &DependantName,
					 MaterializingInfo &EmittedMI);

    void addDependencies(const SymbolStringPtr &Name,
			 const MySymbolDependenceMap &Dependants);

    mutable std::recursive_mutex SessionMutex2;

    // FIXME: Remove this (and runOutstandingMUs) once the linking layer works
    //        with callbacks from asynchronous queries.
    mutable std::recursive_mutex OutstandingMUsMutex;
    std::vector<std::unique_ptr<MyMaterializationUnit>> OutstandingMUs;

    SymbolMap Symbols2;

    // This boxes a materialized unit.  The MU will be automatically freed once all
    // symbols are resolved or the Dylib goes out of scope.
    struct UnmaterializedInfo {
	UnmaterializedInfo(std::unique_ptr<MyMaterializationUnit> MU)
	    : MU(std::move(MU)) {}

	std::unique_ptr<MyMaterializationUnit> MU;
    };

    using UnmaterializedInfosMap =
      DenseMap<SymbolStringPtr, std::shared_ptr<UnmaterializedInfo>>;
    UnmaterializedInfosMap UnmaterializedInfos;


    using MaterializingInfosMap = DenseMap<SymbolStringPtr, MaterializingInfo>;
    MaterializingInfosMap MaterializingInfos;
};

void dylibDefine(MyJITDylib& dylib, std::unique_ptr<MyMaterializationUnit> MU) {
    assert(MU && "Can not define with a null MU");

    std::lock_guard<std::recursive_mutex> Lock(dylib.SessionMutex2);

    for (const std::pair<SymbolStringPtr, JITSymbolFlags> &KV : MU->getSymbols()) {
	assert(!KV.second.isLazy() && "Lazy flag should be managed internally.");
	assert(!KV.second.isMaterializing() && "Materializing flags should be managed internally.");

	SymbolMap::iterator EntryItr;
	bool Added;

	auto NewFlags = KV.second | JITSymbolFlags::Lazy;

        auto r = dylib.Symbols2.insert(std::make_pair(KV.first, JITEvaluatedSymbol(0, NewFlags)));

	if (!r.second) {
	    printf("DUPLICATE!\n");
	    exit(-1);
	}
    }

    auto UMI = std::make_shared<MyJITDylib::UnmaterializedInfo>(std::move(MU));
    for (auto &KV : UMI->MU->getSymbols())
	 dylib.UnmaterializedInfos[KV.first] = UMI;
}

void dylibLodgeQuery(MyJITDylib& dylib,
		     std::shared_ptr<MyAsynchronousSymbolQuery> &Q,
		     const SymbolNameSet& unresolved,
		     bool matchNonExported,
		     MyMaterializationUnitList& MUs) {
    for (auto Name : unresolved) {
	// Search for the name in Symbols. Skip it if not found.
	auto SymI = dylib.Symbols2.find(Name);
	if (SymI == dylib.Symbols2.end()) {
	    printf("XXX Unresolved\n");
	    exit(-1);
	}

	// If this is a non exported symbol and we're skipping those then skip it.
	if (!SymI->second.getFlags().isExported() && !matchNonExported) {
	    printf("XXX Unresolved\n");
	    exit(-1);
	}

	// If the symbol has an address then resolve it.
	if (SymI->second.getAddress() != 0)
	    Q->resolve(Name, SymI->second);

	// If the symbol is lazy, get the MaterialiaztionUnit for it.
	if (SymI->second.getFlags().isLazy()) {
	    assert(SymI->second.getAddress() == 0 &&
		   "Lazy symbol should not have a resolved address");
	    assert(!SymI->second.getFlags().isMaterializing() &&
		   "Materializing and lazy should not both be set");
	    auto UMII = dylib.UnmaterializedInfos.find(Name);
	    assert(UMII != dylib.UnmaterializedInfos.end() &&
		   "Lazy symbol should have UnmaterializedInfo");
	    auto MU = std::move(UMII->second->MU);
	    assert(MU != nullptr && "Materializer should not be null");

	    // Move all symbols associated with this MaterializationUnit into
	    // materializing state.
	    for (auto &KV : MU->getSymbols()) {
		auto SymK = dylib.Symbols2.find(KV.first);
		auto Flags = SymK->second.getFlags();
		Flags &= ~JITSymbolFlags::Lazy;
		Flags |= JITSymbolFlags::Materializing;
		SymK->second.setFlags(Flags);
		dylib.UnmaterializedInfos.erase(KV.first);
	    }

	    // Add MU to the list of MaterializationUnits to be materialized.
	    MUs.push_back(std::move(MU));
        } else {
            if (!SymI->second.getFlags().isMaterializing()) {
	        // The symbol is neither lazy nor materializing, so it must be
	        // ready. Notify the query and continue.
	        Q->notifySymbolReady();
	        continue;
            }
	}

	// Add the query to the PendingQueries list.
	assert(SymI->second.getFlags().isMaterializing() &&
	       "By this line the symbol should be materializing");
	dylib.MaterializingInfos[Name].PendingQueries.push_back(Q);

	bool Added = Q->QueryRegistrations[&dylib].insert(std::move(Name)).second;
	assert(Added && "Duplicate dependence notification?");
    }
}

void runOutstandingMUs(MyJITDylib& dylib) {
    while (1) {
        std::unique_ptr<MyMaterializationUnit> MU;

	{
	    std::lock_guard<std::recursive_mutex> Lock(dylib.OutstandingMUsMutex);
	    if (dylib.OutstandingMUs.empty()) {
		break;
	    } else {
		MU = std::move(dylib.OutstandingMUs.back());
		dylib.OutstandingMUs.pop_back();
	    }
	}

	MU->materialize(dylib);
    }
}

void MyJITDylib::addDependencies(const SymbolStringPtr &Name,
                                 const MySymbolDependenceMap &Dependencies) {
  assert(Symbols2.count(Name) && "Name not in symbol table");
  assert((Symbols2[Name].getFlags().isLazy() ||
          Symbols2[Name].getFlags().isMaterializing()) &&
         "Symbol is not lazy or materializing");

  auto &MI = MaterializingInfos[Name];
  assert(!MI.IsEmitted && "Can not add dependencies to an emitted symbol");

  for (auto &KV : Dependencies) {
    assert(KV.first && "Null JITDylib in dependency?");
    auto &OtherJITDylib = *KV.first;
    auto &DepsOnOtherJITDylib = MI.UnemittedDependencies[&OtherJITDylib];

    for (auto &OtherSymbol : KV.second) {
      auto &OtherMI = OtherJITDylib.MaterializingInfos[OtherSymbol];

      if (OtherMI.IsEmitted)
        transferEmittedNodeDependencies(MI, Name, OtherMI);
      else if (&OtherJITDylib != this || OtherSymbol != Name) {
        OtherMI.Dependants[this].insert(Name);
        DepsOnOtherJITDylib.insert(OtherSymbol);
      }
    }

    if (DepsOnOtherJITDylib.empty())
      MI.UnemittedDependencies.erase(&OtherJITDylib);
  }
}

void MyJITDylib::transferEmittedNodeDependencies(
    MaterializingInfo &DependantMI, const SymbolStringPtr &DependantName,
    MaterializingInfo &EmittedMI) {
  for (auto &KV : EmittedMI.UnemittedDependencies) {
    auto &DependencyJD = *KV.first;
    SymbolNameSet *UnemittedDependenciesOnDependencyJD = nullptr;

    for (auto &DependencyName : KV.second) {
      auto &DependencyMI = DependencyJD.MaterializingInfos[DependencyName];

      // Do not add self dependencies.
      if (&DependencyMI == &DependantMI)
        continue;

      // If we haven't looked up the dependencies for DependencyJD yet, do it
      // now and cache the result.
      if (!UnemittedDependenciesOnDependencyJD)
        UnemittedDependenciesOnDependencyJD =
            &DependantMI.UnemittedDependencies[&DependencyJD];

      DependencyMI.Dependants[this].insert(DependantName);
      UnemittedDependenciesOnDependencyJD->insert(DependencyName);
    }
  }
}

/// Callback to register the dependencies for a given query.
using MyRegisterDependenciesFunction =
    std::function<void(const MySymbolDependenceMap &)>;

/// Search the given JITDylib list for the given symbols.
///
/// SearchOrder lists the JITDylibs to search. For each dylib, the associated
/// boolean indicates whether the search should match against non-exported
/// (hidden visibility) symbols in that dylib (true means match against
/// non-exported symbols, false means do not match).
///
/// The OnResolve callback will be called once all requested symbols are
/// resolved, or if an error occurs prior to resolution.
///
/// The OnReady callback will be called once all requested symbols are ready,
/// or if an error occurs after resolution but before all symbols are ready.
///
/// If all symbols are found, the RegisterDependencies function will be called
/// while the session lock is held. This gives clients a chance to register
/// dependencies for on the queried symbols for any symbols they are
/// materializing (if a MaterializationResponsibility instance is present,
/// this can be implemented by calling
/// MaterializationResponsibility::addDependencies). If there are no
/// dependenant symbols for this query (e.g. it is being made by a top level
/// client to get an address to call) then the value NoDependenciesToRegister
/// can be used.
void sessionLookup(
    MyJITDylib& dylib,
    bool matchNonExported,
    const SymbolNameSet& symbols,
    SymbolsResolvedCallback OnResolve,
    SymbolsReadyCallback OnReady,
    MyRegisterDependenciesFunction RegisterDependencies) {

    // lookup can be re-entered recursively if running on a single thread. Run any
    // outstanding MUs in case this query depends on them, otherwise this lookup
    // will starve waiting for a result from an MU that is stuck in the queue.
    runOutstandingMUs(dylib);

    MyMaterializationUnitList MUs;

    auto Q = std::make_shared<MyAsynchronousSymbolQuery>(symbols, std::move(OnResolve), std::move(OnReady));
    bool QueryIsFullyResolved = false;
    bool QueryIsFullyReady = false;

    {
	std::lock_guard<std::recursive_mutex> Lock(dylib.SessionMutex2);

	dylibLodgeQuery(dylib, Q, symbols, matchNonExported, MUs);

	// Query lodged successfully.

	// Record whether this query is fully ready / resolved. We will use
	// this to call handleFullyResolved/handleFullyReady outside the session
	// lock.
	QueryIsFullyResolved = Q->NotYetResolvedCount == 0;
	QueryIsFullyReady = Q->isFullyReady();

	// Call the register dependencies function.
	if (RegisterDependencies && !Q->QueryRegistrations.empty())
	    RegisterDependencies(Q->QueryRegistrations);
    }

    if (QueryIsFullyResolved)
	Q->handleFullyResolved();
    if (QueryIsFullyReady)
	Q->handleFullyReady();

    // Move the MUs to the OutstandingMUs list, then materialize.
    {
	std::lock_guard<std::recursive_mutex> Lock(dylib.OutstandingMUsMutex);

	for (auto &MU : MUs)
	    dylib.OutstandingMUs.push_back(std::move(MU));
    }

    runOutstandingMUs(dylib);
}

std::string getMangledName(const DataLayout& DL, StringRef Name) {
   std::string MangledName;
   {
       raw_string_ostream MangledNameStream(MangledName);
       Mangler::getNameWithPrefix(MangledNameStream, Name, DL);
   }
   return MangledName;
}

JITEvaluatedSymbol doLookup(std::shared_ptr<SymbolStringPool>& ssp,
			    MyJITDylib& dylib,
			    const DataLayout& dl,
			    const StringRef& initName) {
    // In the threaded case we use promises to return the results.
    std::promise<SymbolMap> PromisedResult;
    std::mutex ErrMutex;
    Error ResolutionError = Error::success();
    std::promise<void> PromisedReady;
    Error ReadyError = Error::success();
    auto OnResolve = [&](Expected<SymbolMap> R) {
			 if (R)
			     PromisedResult.set_value(std::move(*R));
			 else {
			     {
				 ErrorAsOutParameter _(&ResolutionError);
				 std::lock_guard<std::mutex> Lock(ErrMutex);
				 ResolutionError = R.takeError();
			     }
			     PromisedResult.set_value(SymbolMap());
			 }
		     };

    std::function<void(Error)> OnReady(
				       [&](Error Err) {
					   if (Err) {
					       ErrorAsOutParameter _(&ReadyError);
					       std::lock_guard<std::mutex> Lock(ErrMutex);
					       ReadyError = std::move(Err);
					   }
					   PromisedReady.set_value();
				       });

    // Perform the asynchronous lookup.
    SymbolStringPtr Name = ssp->intern(getMangledName(dl, initName));
    SymbolNameSet Symbols({Name});
    sessionLookup(dylib,
		  false,
		  Symbols,
		  OnResolve,
		  OnReady,
		  nullptr);

    auto ResultFuture = PromisedResult.get_future();
    auto&& ResultMap = ResultFuture.get();

    {
	std::lock_guard<std::mutex> Lock(ErrMutex);
	if (ResolutionError) {
	    // ReadyError will never be assigned. Consume the success value.
	    cantFail(std::move(ReadyError));
            outs() << "lookup error: " << ResolutionError;
	    exit(-1);
	}
    }

    auto ReadyFuture = PromisedReady.get_future();
    ReadyFuture.get();

    {
	std::lock_guard<std::mutex> Lock(ErrMutex);
	if (ReadyError) {
            outs() << "lookup error: " << ReadyError;
	    exit(-1);
        }
    }

    assert(ResultMap.size() == 1 && "Unexpected number of results");
    assert(ResultMap.count(Name) && "Missing result for symbol");
    return std::move(ResultMap.begin()->second);
}

class JITDylibSearchOrderResolver : public JITSymbolResolver {
public:
  JITDylibSearchOrderResolver(std::shared_ptr<SymbolStringPool>& ssp,
			      MyJITDylib &JD,
			      SymbolFlagsMap& SymbolFlags)
      : ssp(ssp), JD(JD), SymbolFlags(SymbolFlags) {

  }

  void lookup(const LookupSet &Symbols, OnResolvedFunction OnResolved) {
      // Build an OnResolve callback to unwrap the interned strings and pass them
      // to the OnResolved callback.
      // FIXME: Switch to move capture of OnResolved once we have c++14.
      auto OnResolvedWithUnwrap =
	  [OnResolved](Expected<SymbolMap> InternedResult) {
	      if (!InternedResult) {
		  OnResolved(InternedResult.takeError());
		  return;
	      }

	      LookupResult Result;
	      for (auto &KV : *InternedResult)
		  Result[*KV.first] = std::move(KV.second);
	      OnResolved(Result);
	  };

      // We're not waiting for symbols to be ready. Just log any errors.
      auto OnReady = [](Error Err) {
			 logAllUnhandledErrors(std::move(Err), errs(), "JIT session error: "); };



      // Register dependencies for all symbols contained in this set.
      auto RegisterDependencies =
	  [this](const MySymbolDependenceMap &Deps) {
	      for (auto &KV : SymbolFlags)
		  JD.addDependencies(KV.first, Deps);
	  };
      SymbolNameSet InternedSymbols;

      // Intern the requested symbols: lookup takes interned strings.
      for (auto &S : Symbols)
	  InternedSymbols.insert(ssp->intern(S));
      sessionLookup(JD,
		    true,
		    InternedSymbols,
		    OnResolvedWithUnwrap,
		    OnReady,
		    RegisterDependencies);
  }

  Expected<LookupSet> getResponsibilitySet(const LookupSet &Symbols) {
    LookupSet Result;

    for (auto &KV : SymbolFlags) {
      if (Symbols.count(*KV.first))
        Result.insert(*KV.first);
    }

    return Result;
  }

private:
    std::shared_ptr<SymbolStringPool>& ssp;
    MyJITDylib &JD;
    SymbolFlagsMap& SymbolFlags;
};

static
Error doOnObjLoad(std::shared_ptr<SymbolStringPool> ssp,
		  MyJITDylib& dylib,
		  object::ObjectFile &Obj,
		  std::unique_ptr<RuntimeDyld::LoadedObjectInfo> LoadedObjInfo,
		  std::map<StringRef, JITEvaluatedSymbol> ResolvedRef,
		  std::set<StringRef> &InternalSymbols) {
    SymbolMap Resolved;
    for (auto &KV : ResolvedRef) {
	// Scan the symbols and add them to the Symbols map for resolution.

	// We never claim internal symbols.
	if (InternalSymbols.count(KV.first))
	    continue;
	auto InternedName = ssp->intern(KV.first);
	auto Flags = KV.second.getFlags();

	Resolved[InternedName] = JITEvaluatedSymbol(KV.second.getAddress(), Flags);
    }

    MyJITDylib::AsynchronousSymbolQuerySet FullyResolvedQueries;
    {
	std::lock_guard<std::recursive_mutex> Lock(dylib.SessionMutex2);
	for (const auto &KV : Resolved) {
	    auto &Name = KV.first;
	    auto Sym = KV.second;

	    assert(!Sym.getFlags().isLazy() && !Sym.getFlags().isMaterializing() &&
		   "Materializing flags should be managed internally");

	    auto I = dylib.Symbols2.find(Name);

	    assert(I != dylib.Symbols2.end() && "Symbol not found");
	    assert(!I->second.getFlags().isLazy() &&
		   I->second.getFlags().isMaterializing() &&
		   "Symbol should be materializing");
	    assert(I->second.getAddress() == 0 && "Symbol has already been resolved");

	    assert((Sym.getFlags() & ~JITSymbolFlags::Weak) ==
		   (JITSymbolFlags::stripTransientFlags(I->second.getFlags()) &
		    ~JITSymbolFlags::Weak) &&
		   "Resolved flags should match the declared flags");

	    // Once resolved, symbols can never be weak.
	    JITSymbolFlags ResolvedFlags = Sym.getFlags();
	    ResolvedFlags &= ~JITSymbolFlags::Weak;
	    ResolvedFlags |= JITSymbolFlags::Materializing;
	    I->second = JITEvaluatedSymbol(Sym.getAddress(), ResolvedFlags);

	    auto &MI = dylib.MaterializingInfos[Name];
	    for (auto &Q : MI.PendingQueries) {
		Q->resolve(Name, Sym);
		if (Q->NotYetResolvedCount == 0)
		    FullyResolvedQueries.insert(Q);
	    }
	}
    }

    for (auto &Q : FullyResolvedQueries) {
	assert(Q->NotYetResolvedCount == 0 && "Q not fully resolved");
	Q->handleFullyResolved();
    }

    return Error::success();
}

void doOnObjEmit(MyJITDylib& dylib,
		 SymbolFlagsMap& Emitted,
		 Error Err) {
    if (Err) {
	logAllUnhandledErrors(std::move(Err), errs(), "JIT session error: ");
	exit(-1);
    }

    MyJITDylib::AsynchronousSymbolQuerySet readyQueries;
    {
	std::lock_guard<std::recursive_mutex> Lock(dylib.SessionMutex2);

	for (const auto &KV : Emitted) {
	    const auto &Name = KV.first;

	    auto MII = dylib.MaterializingInfos.find(Name);
	    assert(MII != dylib.MaterializingInfos.end() &&
		   "Missing MaterializingInfo entry");

	    auto &MI = MII->second;

	    // For each dependant, transfer this node's emitted dependencies to
	    // it. If the dependant node is ready (i.e. has no unemitted
	    // dependencies) then notify any pending queries.
	    for (auto &KV : MI.Dependants) {
		auto &DependantJD = *KV.first;
		for (auto &DependantName : KV.second) {
		    auto DependantMII =
			DependantJD.MaterializingInfos.find(DependantName);
		    assert(DependantMII != DependantJD.MaterializingInfos.end() &&
			   "Dependant should have MaterializingInfo");

		    auto &DependantMI = DependantMII->second;

		    // Remove the dependant's dependency on this node.
		    assert(DependantMI.UnemittedDependencies[&dylib].count(Name) &&
			   "Dependant does not count this symbol as a dependency?");
		    DependantMI.UnemittedDependencies[&dylib].erase(Name);
		    if (DependantMI.UnemittedDependencies[&dylib].empty())
			DependantMI.UnemittedDependencies.erase(&dylib);

		    // Transfer unemitted dependencies from this node to the dependant.
		    DependantJD.transferEmittedNodeDependencies(DependantMI, DependantName, MI);

		    // If the dependant is emitted and this node was the last of its
		    // unemitted dependencies then the dependant node is now ready, so
		    // notify any pending queries on the dependant node.
		    if (DependantMI.IsEmitted
			&& DependantMI.UnemittedDependencies.empty()) {

			assert(DependantMI.Dependants.empty() &&
			       "Dependants should be empty by now");
			for (auto &Q : DependantMI.PendingQueries) {
			    assert(Q->NotYetReadyCount != 0 && "All symbols already emitted");
			    if (--(Q->NotYetReadyCount) == 0) {
				readyQueries.insert(Q);
			    }
			    Q->removeQueryDependence(DependantJD, DependantName);
			}

			// Since this dependant is now ready, we erase its MaterializingInfo
			// and update its materializing state.
			assert(DependantJD.Symbols2.count(DependantName) &&
			       "Dependant has no entry in the Symbols table");
			auto& DependantSym = DependantJD.Symbols2[DependantName];
			DependantSym.setFlags(DependantSym.getFlags() &  ~JITSymbolFlags::Materializing);
			DependantJD.MaterializingInfos.erase(DependantMII);
		    }
		}
	    }
	    MI.Dependants.clear();
	    MI.IsEmitted = true;

	    if (MI.UnemittedDependencies.empty()) {
		for (auto &Q : MI.PendingQueries) {
		    Q->notifySymbolReady();
		    if (Q->isFullyReady())
			readyQueries.insert(Q);
		    Q->removeQueryDependence(dylib, Name);
		}
		assert(dylib.Symbols2.count(Name) &&
		       "Symbol has no entry in the Symbols table");
		auto &Sym = dylib.Symbols2[Name];
		Sym.setFlags(Sym.getFlags() & ~JITSymbolFlags::Materializing);
		dylib.MaterializingInfos.erase(MII);
	    }
	}
    }

    for (auto &Q : readyQueries) {
	assert(Q->isFullyReady() && "Q is not fully ready");
	Q->handleFullyReady();
    }

    Emitted.clear();
}

void doEmit(std::shared_ptr<SymbolStringPool>& ssp,
	    std::mutex& RTDyldLayerMutex,
	    std::vector<std::unique_ptr<RuntimeDyld::MemoryManager>>& MemMgrs,
	    MyJITDylib &JD,
	    SymbolFlagsMap SymbolFlags,
	    std::unique_ptr<MemoryBuffer> O) {
    assert(O && "Object must not be null");

    auto Obj = object::ObjectFile::createObjectFile(*O);

    if (!Obj) {
	logAllUnhandledErrors(Obj.takeError(), errs(), "JIT session error: ");
	exit(-1);
    }


    // Collect the internal symbols from the object file: We will need to
    // filter these later.
    auto InternalSymbols = std::make_shared<std::set<StringRef>>();
    {
	for (auto &Sym : (*Obj)->symbols()) {
	    if (Sym.getFlags() & object::BasicSymbolRef::SF_Global)
		continue;

	    if (auto SymName = Sym.getName()) {
		InternalSymbols->insert(*SymName);
	    } else {
		logAllUnhandledErrors(SymName.takeError(), errs(), "JIT session error: ");
		exit(-1);
	    }
	}
    }

    RuntimeDyld::MemoryManager *MemMgr = nullptr;

    // Create a record a memory manager for this object.
    {
	auto Tmp = std::make_unique<SectionMemoryManager>(); ;
	std::lock_guard<std::mutex> Lock(RTDyldLayerMutex);
	MemMgrs.push_back(std::move(Tmp));
	MemMgr = MemMgrs.back().get();
    }

    // This method launches an asynchronous link step that will fulfill our
    // materialization responsibility. We need to switch R to be heap
    // allocated before that happens so it can live as long as the asynchronous
    // link needs it to (i.e. it must be able to outlive this method).
    auto SharedSyms = std::make_shared<SymbolFlagsMap>(std::move(SymbolFlags));

    JITDylibSearchOrderResolver Resolver(ssp, JD, *SharedSyms);

    /* Thoughts on proper cross-dylib weak symbol handling:
     *
     * Change selection of canonical defs to be a manually triggered process, and
     * add a 'canonical' bit to symbol definitions. When canonical def selection
     * is triggered, sweep the JITDylibs to mark defs as canonical, discard
     * duplicate defs.
     */
    bool ProcessAllSections = false;
    jitLinkForORC(
      **Obj, std::move(O), *MemMgr, Resolver, ProcessAllSections,
      [ssp, &JD, &Obj, InternalSymbols](
          std::unique_ptr<RuntimeDyld::LoadedObjectInfo> LoadedObjInfo,
          std::map<StringRef, JITEvaluatedSymbol> ResolvedSymbols) {
	  return doOnObjLoad(ssp, JD, **Obj, std::move(LoadedObjInfo),
			     ResolvedSymbols, *InternalSymbols);
      },
      [&JD,SharedSyms](Error Err) {
	  doOnObjEmit(JD, *SharedSyms, std::move(Err));
      });
}

/// MaterializationUnit that materializes modules by calling the 'emit' method
/// on the given IRLayer.
class Custom2IRLayerMaterializationUnit : public MyMaterializationUnit {
public:
    using SymbolNameToDefinitionMap = std::map<SymbolStringPtr, GlobalValue *>;
private:
    SymbolFlagsMap SymbolFlags;

    std::unique_ptr<LLVMContext> Ctx;
    std::unique_ptr<Module> M;

    SymbolNameToDefinitionMap SymbolToDefinition;

    JITTargetMachineBuilder JTMB;
    std::shared_ptr<SymbolStringPool>& ssp;
    std::mutex& RTDyldLayerMutex;
    std::vector<std::unique_ptr<RuntimeDyld::MemoryManager>>& MemMgrs;
public:
    Custom2IRLayerMaterializationUnit(std::shared_ptr<SymbolStringPool>& ssp,
				      JITTargetMachineBuilder& jtmb,
				      std::mutex& RTDyldLayerMutex,
				      std::vector<std::unique_ptr<RuntimeDyld::MemoryManager>>& MemMgrs,
				      std::unique_ptr<LLVMContext> ctx,
                                      std::unique_ptr<Module> M)
	: SymbolFlags(),
	  Ctx(std::move(ctx)),
          M(std::move(M)),
	  SymbolToDefinition(),
	  JTMB(jtmb),
	  ssp(ssp),
	  RTDyldLayerMutex(RTDyldLayerMutex),
	  MemMgrs(MemMgrs) {

	llvm::Module* m = this->M.get();

        const DataLayout& DL = m->getDataLayout();
        // Add symbols with mangled names.
	for (auto &G : m->getFunctionList()) {
	    if (G.hasName()
		&& !G.isDeclaration()
		&& !G.hasLocalLinkage()
		&& !G.hasAvailableExternallyLinkage()
		&& !G.hasAppendingLinkage()) {

                auto MangledName = ssp->intern(getMangledName(DL, G.getName()));
		SymbolFlags[MangledName] = JITSymbolFlags::fromGlobalValue(G);
		SymbolToDefinition[MangledName] = &G;
	    }
	}
    }

    const SymbolFlagsMap& getSymbols() const override { return SymbolFlags; }

private:
    void materialize(MyJITDylib &JD) override {
	// Throw away the SymbolToDefinition map: it's not usable after we hand
	// off the module.
	SymbolToDefinition.clear();

	assert(M.get() && "Module must not be null");


	auto TM = cantFail(JTMB.createTargetMachine());

	SmallVector<char, 0> ObjBufferSV;

	{
	    raw_svector_ostream ObjStream(ObjBufferSV);

	    legacy::PassManager PM;
	    MCContext *Ctx;
	    if (TM->addPassesToEmitMC(PM, Ctx, ObjStream))
		llvm_unreachable("Target does not support MC emission.");
	    PM.run(*M);
	}

	auto ObjBuffer =
	    llvm::make_unique<SmallVectorMemoryBuffer>(std::move(ObjBufferSV));
	auto Obj =
	    object::ObjectFile::createObjectFile(ObjBuffer->getMemBufferRef());

	if (Obj) {
	    M = nullptr;
	    Ctx = nullptr;
            doEmit(ssp, RTDyldLayerMutex, MemMgrs, JD, std::move(SymbolFlags),
		   std::move(ObjBuffer));
	} else {
	    logAllUnhandledErrors(Obj.takeError(), errs(), "JIT session error: ");
	    exit(-1);
	}
    }

    void discard(const MyJITDylib &JD, const SymbolStringPtr &Name) override {
	SymbolFlags.erase(Name);
	auto I = SymbolToDefinition.find(Name);
	assert(I != SymbolToDefinition.end() &&
	       "Symbol not provided by this MU, or previously discarded");
	assert(!I->second->isDeclaration() &&
	       "Discard should only apply to definitions");
	I->second->setLinkage(GlobalValue::AvailableExternallyLinkage);
	SymbolToDefinition.erase(I);
    }
};


void addModule(std::shared_ptr<SymbolStringPool>& ssp,
	       MyJITDylib& dylib,
	       JITTargetMachineBuilder& jtmb,
	       std::mutex& mut,
	       std::vector<std::unique_ptr<RuntimeDyld::MemoryManager>>& memMgrs,
	       const char* path,
	       moduleFn f) {
    auto ctx = std::make_unique<LLVMContext>();
    auto m = f(ctx.get(), path);
    std::unique_ptr<MyMaterializationUnit> p(
	new Custom2IRLayerMaterializationUnit(ssp, jtmb, mut, memMgrs, std::move(ctx), std::move(m)));
    dylibDefine(dylib, std::move(p));
}

/// Materializes the given object file (represented by a MemoryBuffer
/// instance) by calling 'emit' on the given ObjectLayer.
class LasicObjectLayerMaterializationUnit : public MyMaterializationUnit {
public:
    LasicObjectLayerMaterializationUnit(std::shared_ptr<SymbolStringPool>& ssp,
					std::mutex& mutex,
					std::vector<std::unique_ptr<RuntimeDyld::MemoryManager>>& memMgrs,
					std::unique_ptr<MemoryBuffer> O,
					SymbolFlagsMap SymbolFlags)
	: SymbolFlags(std::move(SymbolFlags)),
	  ssp(ssp),
	  RTDyldLayerMutex(mutex),
	  MemMgrs(memMgrs),
	  O(std::move(O)) {}

    const SymbolFlagsMap& getSymbols() const override { return SymbolFlags; }

private:

    void materialize(MyJITDylib &JD) override {
	doEmit(ssp, RTDyldLayerMutex, MemMgrs, JD, std::move(SymbolFlags), std::move(O));
    }

    void discard(const MyJITDylib &JD, const SymbolStringPtr &Name) override {
	SymbolFlags.erase(Name);
	// FIXME: Support object file level discard. This could be done by building a
	//        filter to pass to the object layer along with the object itself.
    }

    SymbolFlagsMap SymbolFlags;
    std::shared_ptr<SymbolStringPool>& ssp;
    std::mutex& RTDyldLayerMutex;
    std::vector<std::unique_ptr<RuntimeDyld::MemoryManager>>& MemMgrs;
    std::unique_ptr<MemoryBuffer> O;
};

/// Returns a SymbolFlagsMap for the object file represented by the given
/// buffer, or an error if the buffer does not contain a valid object file.
Expected<SymbolFlagsMap> myGetObjectSymbolFlags(std::shared_ptr<SymbolStringPool> ssp,
                                                MemoryBufferRef ObjBuffer) {
  auto Obj = object::ObjectFile::createObjectFile(ObjBuffer);

  if (!Obj)
    return Obj.takeError();

  SymbolFlagsMap SymbolFlags;
  for (auto &Sym : (*Obj)->symbols()) {
    // Skip symbols not defined in this object file.
    if (Sym.getFlags() & object::BasicSymbolRef::SF_Undefined)
      continue;

    // Skip symbols that are not global.
    if (!(Sym.getFlags() & object::BasicSymbolRef::SF_Global))
      continue;

    auto Name = Sym.getName();
    if (!Name)
      return Name.takeError();
    auto InternedName = ssp->intern(*Name);
    auto SymFlags = JITSymbolFlags::fromObjectSymbol(Sym);
    if (!SymFlags)
      return SymFlags.takeError();
    SymbolFlags[InternedName] = std::move(*SymFlags);
  }

  return SymbolFlags;
}

/* Load the file at the given path and at it to the main dynamic
   library in the object layer */
void addObjectFile(std::shared_ptr<SymbolStringPool>& ssp,
	           MyJITDylib& dylib,
		   std::mutex& mutex,
		   std::vector<std::unique_ptr<RuntimeDyld::MemoryManager>>& memMgrs,
		   const char* path) {
    auto objBuffer = fromFile(path);

    auto SymbolFlags = myGetObjectSymbolFlags(ssp, objBuffer->getMemBufferRef());

    if (!SymbolFlags) {
        fprintf(stderr, "Failed to add object file %s.\n", path);
	exit(-1);
    }

    std::unique_ptr<MyMaterializationUnit> ObjMU(
        new LasicObjectLayerMaterializationUnit(ssp, mutex, memMgrs, std::move(objBuffer),
		         		        std::move(*SymbolFlags)));
    dylibDefine(dylib, std::move(ObjMU));
}

int main(int argc, const char** argv) {
    LLVMInitializeX86TargetInfo();
    LLVMInitializeX86TargetMC();
    LLVMInitializeX86Target();
    LLVMInitializeX86AsmPrinter();

    Triple triple(sys::getProcessTriple());
    JITTargetMachineBuilder jtmb(triple);

    auto ssp = std::make_shared<SymbolStringPool>();
    MyJITDylib dylib;
    std::mutex RTDyldLayerMutex;
    std::vector<std::unique_ptr<RuntimeDyld::MemoryManager>> memMgrs;
    const DataLayout& dl = getProcessDataLayout(jtmb);

    const auto begin = high_resolution_clock::now();

    addObjectFile(ssp, dylib, RTDyldLayerMutex, memMgrs, "add.o");

    //addModule(ssp, dylib, jtmb, RTDyldLayerMutex, memMgrs, "add.cpp", compileCPP);
    addModule(ssp, dylib, jtmb, RTDyldLayerMutex, memMgrs, "fib.c", compileC);

    JITEvaluatedSymbol sym = doLookup(ssp, dylib, dl, "fib");

    auto fib = (fib_fn) sym.getAddress();

    // Get time to add
    auto time = high_resolution_clock::now() - begin;

    for (uint64_t i = 0; i != 10; ++i) {
	printf("fib(%llu) = %llu\n", i, fib(i));
    }

    std::cout << "Elapsed time: " << duration<double, std::milli>(time).count() << ".\n";

    return 0;
}
