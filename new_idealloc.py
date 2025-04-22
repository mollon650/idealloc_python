# idealloc Python 版本完整实现
# =====================================
# 文件结构:
# idealloc/
# ├── models.py
# ├── helpers.py
# ├── instance.py
# ├── analyze.py
# ├── boxing.py
# ├── placement.py
# └── cli.py

# ---------- models.py ----------
from typing import List, Optional
import math, random, sys
from typing import List, Dict, Set, Tuple, Optional, Union, Any
import time
from typing import NewType
ByteSteps = NewType('ByteSteps', int)
import itertools

_id_counter = itertools.count(start=2**32 - 1, step=-1)  # mimic AtomicU32::new(u32::MAX)

def get_total_originals_boxed(jobs: List['Job']) -> int:
    """Sum of originals_boxed across all jobs."""
    return sum(j.originals_boxed for j in jobs)

class Info:
    """Stores useful information about an Instance."""
    __slots__ = ('load', 'min_max_height')

    def __init__(self):
        # load: maximum load, or None if not set
        self.load: Optional[int] = None
        # min_max_height: (min_height, max_height), or None if not set
        self.min_max_height: Optional[Tuple[int,int]] = None

    @staticmethod
    def merge(a: 'Instance', b: 'Instance') -> 'Info':
        info = Info()
        min1, max1 = a.min_max_height()
        min2, max2 = b.min_max_height()
        info.min_max_height = (min(min1, min2), max(max1, max2))
        return info

    def set_load(self, l: int):
        self.load = l

    def set_heights(self, heights: Tuple[int,int]):
        self.min_max_height = heights

class Instance:
    """Representation of a DSA instance for idealloc."""
    def __init__(self, jobs: List['Job']):
        self.jobs: List[Job] = jobs
        self.info: Info = Info()

    def make_buckets(self, epsilon: float) -> Dict[int, 'Instance']:
        """
        Splits into unit-height buckets per Corollary 15.
        Each bucket keyed by the height used for Theorem 2.
        """
        result: Dict[int, Instance] = {}
        prev_floor = 1.0 / (1.0 + epsilon)
        source = self
        i = 0
        while source.jobs:
            h = (1.0 + epsilon) ** i
            # select jobs in (prev_floor, h]
            if any(prev_floor < j.size <= h for j in source.jobs):
                h_split = math.floor(h)
                small, rem = source.split_by_height(h_split)
                result[h_split] = small
                source = rem
            prev_floor = h
            i += 1
        return result

    def check_boxed_originals(self, target: int) -> bool:
        """Return True if exactly `target` original jobs have been boxed."""
        # from helpe import get_total_originals_boxed
        return target == get_total_originals_boxed(self.jobs)

    def get_safety_info(self, epsilon: float) -> Tuple[float,float,float,bool]:
        """
        Returns (r, mu, H, safe_flag):
          r = h_max / h_min
          mu = epsilon / (log2 r)^2
          H  = ceil(mu^5 * h_max / (log2 r)^2)
          safe_flag = mu < x1 && target_size >= h_min
        """
        h_min, h_max = self.min_max_height()
        x1, _, _, lg2r = self.ctrl_prelude()
        mu = epsilon / lg2r
        H = math.ceil((mu**5 * h_max) / lg2r)
        target_size = math.floor(mu * H)
        safe = (mu < x1) and (target_size >= h_min)
        return (h_max / h_min, mu, float(H), safe)

    def get_horizon(self) -> Tuple[int,int]:
        """Return (smallest birth, largest death) across all jobs."""
        births = [j.birth for j in self.jobs]
        deaths = [j.death for j in self.jobs]
        return (min(births), max(deaths))

    def min_max_height(self) -> Tuple[int,int]:
        """Return (min_height, max_height) of jobs, caching result."""
        if self.info.min_max_height is not None:
            return self.info.min_max_height
        heights = [j.size for j in self.jobs]
        mn, mx = min(heights), max(heights)
        self.info.min_max_height = (mn, mx)
        return (mn, mx)

    def split_by_height(self, ceil: int) -> Tuple['Instance','Instance']:
        """Split into two Instances: jobs with size <= ceil, and > ceil."""
        small = [j for j in self.jobs if j.size <= ceil]
        high  = [j for j in self.jobs if j.size > ceil]
        return (Instance(small), Instance(high))

    # def split_by_liveness(self, pts: Set[int]) -> Tuple[List['Job'], Dict[int,'Instance']]:
    #     """
    #     Split into (live_jobs, {idx: Instance}) per Buchsbaum's algorithm.
    #     Returns jobs live across segments, and mapping from point index to Instance.
    #     """
    #     # from helpe import get_events
    #     sorted_pts = sorted(pts)
    #     live_jobs: List['Job'] = []
    #     x_is: Dict[int,List['Job']] = {i:[] for i in range(len(sorted_pts)-1)}
    #     jobs_sorted = sorted(self.jobs, key=lambda j: j.birth)
    #     idx = 0
    #     n = len(jobs_sorted)
    #     for i in range(len(sorted_pts)-1):
    #         start, end = sorted_pts[i], sorted_pts[i+1]
    #         while idx < n:
    #             j = jobs_sorted[idx]
    #             if j.death <= start:
    #                 idx += 1
    #                 continue
    #             if j.birth >= end:
    #                 break
    #             if j.birth >= start and j.death <= end:
    #                 x_is[i].append(j)
    #             else:
    #                 live_jobs.append(j)
    #             idx += 1
    #     # Convert each bucket to Instance, return
    #     return live_jobs, {i: Instance(lst) for i,lst in x_is.items()}

    def split_by_liveness(
        self,
        pts: Set[ByteSteps]
    ) -> Tuple[List['Job'], Dict[ByteSteps, "Instance"]]:
        """
        等价于 Rust 版本：
        返回二元组 (live, { q -> Instance(X_i) })
        - live  : 在下一个关键点 t_{q+1} 仍活跃的 jobs
        - X_i   : 完全落在 (t_q, t_{q+1}) 区间内的 jobs
        """
        # --- 1. 准备容器 -----------------------------------------------------
        x_is_base: Dict[ByteSteps, List[Job]] = {}
        live: List[Job] = []

        # --- 2. 关键点序列 vec<t_q> 和 jobs 排序 -----------------------------
        pts_vec: List[ByteSteps] = sorted(pts)
        # Rust: self.jobs[..].sort_unstable()
        jobs_sorted = sorted(self.jobs)   # 依 dataclass(order=True) -> birth 升序
        idx = 0                           # 游标指向未处理的最小 birth job

        # --- 3. 主循环 -------------------------------------------------------
        q_iter = iter(enumerate(pts_vec))
        while True:
            try:
                q, t_q = next(q_iter)
            except StopIteration:
                break  # 理论不会走到这一步

            # t_q_next 是否存在？
            try:
                q_next, t_q_next = next(q_iter)
                # 先把迭代器“回滚”一步，相当于 peek
                q_iter = (_ for _ in [(q_next, t_q_next)] + list(q_iter))
                is_last_segment = (q_next == len(pts_vec) - 1)
            except StopIteration:
                break  # 没有下一个点，跳出

            if is_last_segment:
                # Rust 注释：最后一段，全归入当前 X_i
                while idx < len(jobs_sorted):
                    job = jobs_sorted[idx]
                    idx += 1
                    x_is_base.setdefault(q, []).append(job)
                break  # 处理完直接退出

            # 非最后一段：尽可能处理当前区间
            while idx < len(jobs_sorted):
                job = jobs_sorted[idx]
                if job.lives_within((t_q, t_q_next)):
                    idx += 1
                    x_is_base.setdefault(q, []).append(job)
                elif job.is_live_at(t_q_next):
                    idx += 1
                    live.append(job)
                else:
                    # 该 job.birth >= t_q_next，留到下一段处理
                    break

        # --- 4. 构造返回值 ---------------------------------------------------
        x_i_instances: Dict[ByteSteps, Instance] = {
            k: Instance(v) for k, v in x_is_base.items()
        }
        return live, x_i_instances

    def total_originals_boxed(self) -> int:
        """Count how many originals boxed (via helpe.get_total_originals_boxed)."""
        # from helpe import get_total_originals_boxed
        return get_total_originals_boxed(self.jobs)

    def merge_with(self, other: 'Instance') -> 'Instance':
        """Return a new Instance merging self.jobs + other.jobs, merging Info."""
        merged = Instance(self.jobs + other.jobs)
        merged.info = Info.merge(self, other)
        return merged

    def merge_via_ref(self, other: 'Instance') -> None:
        """In-place merge of another Instance into this one."""
        self.jobs.extend(other.jobs)
        self.info = Info.merge(self, other)

    def ctrl_prelude(self) -> Tuple[float,float,float,float]:
        """Compute (x1, small_end, big_end, lg2r) per Theorem 16 proof."""
        h_min, h_max = self.min_max_height()
        r = h_max / h_min
        lgr = math.log2(r)
        lg2r = lgr**2
        small_end = (lg2r**7 / r)**(1/6)
        mu_lim = (math.sqrt(5) - 1) / 2
        big_end = mu_lim * lg2r
        return (mu_lim, small_end, big_end, lg2r)

from dataclasses import dataclass, field
from typing import Optional, List

@dataclass(order=True)
class Job:
    """
    Python equivalent of the Rust `Job` struct.
    Attributes:
      birth:     start time (exclusive)
      death:     end time (exclusive)
      size:      allocated size or box height
      req_size:  requested size
      alignment: optional alignment requirement
      contents:  None for originals or list of boxed jobs
      originals_boxed: number of original jobs contained
      id:        unique identifier
    """
    birth:     int
    death:     int
    size:      int
    req_size:  int
    alignment: Optional[int]
    contents:  Optional[List['Job']]
    originals_boxed: int
    id:        int = field(compare=False)

    def overlaps_with(self, other: 'Job') -> bool:
        return not (self.birth >= other.death or other.birth >= self.death)

    def get_id(self) -> int:
        return self.id

    def get_req_size(self) -> int:
        return self.req_size

    def get_alignment(self) -> Optional[int]:
        return self.alignment

    @staticmethod
    def new() -> 'Job':
        """
        Creates a dummy Job with default zeroed fields.
        """
        return Job(0, 0, 0, 0, None, None, 0, 0)

    # @staticmethod
    # def new_box(contents: List['Job'], height: int) -> 'Job':
    #     """
    #     Creates a box Job containing `contents`, height=box size.
    #     Sorts contents by size desc, computes bounding birth/death.
    #     """
    #     sorted_contents = sorted(contents, key=lambda j: j.size, reverse=True)
    #     birth = min(j.birth for j in sorted_contents)
    #     death = max(j.death for j in sorted_contents)
    #     originals = sum(1 if j.contents is None else j.originals_boxed for j in sorted_contents)
    #     # assign negative IDs for newly created boxes if desired
    #     return Job(birth, death, height, height, None, sorted_contents, originals, id=-1)
    
    @staticmethod
    def new_box(contents: List['Job'], height: ByteSteps) -> 'Job':
        """
        Creates a by‑guarantee valid 'box' Job that encloses all `contents`,
        mirroring the Rust implementation.
        """
        # 0) sort "big rocks first"
        contents.sort(key=lambda j: j.size, reverse=True)

        # 1) assert enclosure
        assert get_load(contents) <= height, "Bad boxing requested"

        # 2) compute bounding birth/death
        birth = min(j.birth for j in contents)
        death = max(j.death for j in contents)

        # 3) count originals boxed
        originals_boxed = sum(
            1 if j.is_original() else j.originals_boxed
            for j in contents
        )

        # 4) allocate unique id
        box_id = next(_id_counter)
        assert box_id != 2**32 // 2 + 1, "ID overflow sentinel hit"

        # 5) create new Job (the box)
        return Job(
        size            = height,
        birth           = birth,
        death           = death,
        req_size        = height,
        alignment       = None,
        contents        = contents,
        originals_boxed = originals_boxed,
        id              = box_id,
    )

    def is_live_at(self, t: int) -> bool:
        return self.birth < t and self.death > t

    def lives_within(self, space: Tuple[int, int]) -> bool:
        return self.birth >= space[0] and self.death <= space[1]

    def is_original(self) -> bool:
        return self.contents is None

    def dies_before(self, t: int) -> bool:
        return self.death <= t

    def born_after(self, t: int) -> bool:
        return self.birth >= t

    def lifetime(self) -> int:
        return self.death - self.birth - 1

    def area(self) -> int:
        return self.size * self.lifetime()

class PlacedJob:
    """
    Represents a Job assigned an offset in address space, tracking squeezes.
    """
    def __init__(self, descr: Job, offset: int = 0):
        # descr: underlying Job descriptor
        self.descr: Job = descr
        # offset within address space
        self.offset: int = offset
        # count of how many times squeezed
        self.times_squeezed: int = 0

    def overlaps_with(self, other: 'PlacedJob') -> bool:
        """
        True if self and other overlap in time.
        """
        return (
            self.descr.birth < other.descr.death and
            other.descr.birth < self.descr.death
        )

    def next_avail_offset(self) -> int:
        """Return offset plus job size."""
        return self.offset + self.descr.size

    def get_corrected_offset(self, start_addr: int, cand: int) -> int:
        """
        Returns a candidate offset aligned according to descr.alignment.
        """
        a = self.descr.alignment
        if a is not None:
            cand_addr = start_addr + cand
            if cand_addr == 0 or cand_addr % a == 0:
                return cand
            elif cand_addr < a:
                return a - start_addr
            else:
                # round up to next multiple of a, then subtract start
                return (cand_addr // a + 1) * a - start_addr
        return cand

    def __lt__(self, other: 'PlacedJob') -> bool:
        """
        For heapq: compare by offset (min-heap on offset).
        """
        return self.offset < other.offset

    def __eq__(self, other: Any) -> bool:
        """Equality based on underlying job ID."""
        return isinstance(other, PlacedJob) and self.descr.id == other.descr.id

    def __hash__(self) -> int:
        """Hash based on underlying job ID."""
        return hash(self.descr.id)

class VertStripJob:
    """
    Helper struct for Lemma 1 vertical strips (max-heap by death time).
    """
    def __init__(self, job: Job):
        self.job = job

    def __lt__(self, other: 'VertStripJob') -> bool:
        # Invert comparison for max-heap: larger death first
        return self.job.death > other.job.death

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, VertStripJob) and self.job == other.job

class HorStripJob:
    """
    Helper struct for Lemma 1 horizontal strips (max-heap by birth time).
    """
    def __init__(self, job: Job):
        self.job = job

    def __lt__(self, other: 'HorStripJob') -> bool:
        # Invert comparison for max-heap: larger birth first
        return self.job.birth > other.job.birth

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, HorStripJob) and self.job == other.job


def strip_box_core(
    strips: List[Any],
    group_size: ByteSteps,
    box_size: ByteSteps
) -> List[Job]:
    """
    Splits each strip into boxes of at most `group_size` jobs,
    boxing them with real size `box_size`.
    """
    res: List[Job] = []
    buf: List[Job] = []
    for strip in strips:
        count = 0
        # strip is a max-heap of VertStripJob or HorStripJob
        while strip:
            entry = heapq.heappop(strip)
            buf.append(entry.job)
            count += 1
            if count == group_size or not strip:
                res.append(Job.new_box(buf, box_size))
                buf = []
                count = 0
    return res


def strip_boxin(
    verticals: List[List[VertStripJob]],
    horizontals: List[List[HorStripJob]],
    group_size: ByteSteps,
    box_size: ByteSteps
) -> List[Job]:
    """
    Applies `strip_box_core` to both vertical and horizontal strips,
    concatenating the resulting boxed JobSets.
    """
    res = strip_box_core(verticals, group_size, box_size)
    res.extend(strip_box_core(horizontals, group_size, box_size))
    return res


def strip_cuttin(
    source: 'IndexMap',
    mirror: 'IndexMap',
    to_take: ByteSteps,
    use_vertical: bool = True
) -> list[Any]:
    """
    等价于 Rust 版 strip_cuttin：
    - source: IndexMap[u32, Job]，支持 pop() 弹出最后插入的 (key, Job)
    - mirror: IndexMap[u32, Job]，同样内容，做镜像以便同步删掉
    - to_take: 要提取的作业数
    - T: 必须定义 `T.new(Job) -> T` 并实现 __lt__ 以支持 heapq
    
    返回一个 List[T]，其内部已经是一个二叉堆（最大堆，依赖 T.__lt__）。
    """
    res = []
    stripped = 0

    while stripped < to_take and len(source) > 0:
        # 1) 从 source 弹出最后插入的 (id, Job)
        job_id, cut_job = source.pop()
        # 2) 同步从 mirror 删除该 id
        mirror.shift_remove(job_id)
        # 3) 用 T.new 构造新元素并推入堆
        elem = VertStripJob(cut_job) if use_vertical else HorStripJob(cut_job)
        heapq.heappush(res, elem)
        stripped += 1

    return res

# def strip_cuttin(
#     source: 'IndexMap',
#     mirror: 'IndexMap',
#     to_take: ByteSteps,
#     use_vertical: bool = True
# ) -> List[Any]:
#     """
#     Removes up to `to_take` jobs from `source`, also removing from `mirror`,
#     and returns a max-heap (list) of helper jobs (VertStripJob or HorStripJob).
#     Set `use_vertical=False` to produce HorStripJob entries.
#     """
#     heap: List[Any] = []
#     taken = 0
#     # source is an ordered dict mapping id->Job
#     while taken < to_take and source:
#         job_id, job = source.popitem()
#         mirror.pop(job_id, None)
#         entry = VertStripJob(job) if use_vertical else HorStripJob(job)
#         heapq.heappush(heap, entry)
#         taken += 1
#     return heap

    
# ---------- helpers.py ----------
import heapq
from dataclasses import dataclass
from typing import List, Tuple
# from models import Job
from enum import IntEnum

class T2Control:
    """
    Helper structure for Theorem 2 controlling bounding interval and critical points.
    """
    def __init__(self, jobs: Any = None,
                 bounding_interval: Optional[Tuple[ByteSteps, ByteSteps]] = None,
                 critical_points: Optional[Set[ByteSteps]] = None):
        if critical_points is not None and bounding_interval is not None:
            # Construct from explicit parameters
            self.bounding_interval = bounding_interval
            self.critical_points = (sorted(critical_points))
        else:
            # Initialize from jobs instance
            assert isinstance(jobs, Instance), "jobs must be Instance"
            start, end = jobs.get_horizon()
            assert start < end, "Same-ends horizon met."
            mid = T2Control.gen_crit(jobs, start, end)
            self.bounding_interval = (start, end)
            self.critical_points = {start, end, mid}
            self.critical_points = (sorted(self.critical_points))

    @staticmethod
    def gen_crit(jobs: Instance, left: ByteSteps, right: ByteSteps) -> ByteSteps:
        """
        Generates a random critical point v in (left, right) such that
        at least one job in `jobs` is live at v.
        """
        assert left + 1 < right, "Bad range found."
        pts: List[ByteSteps] = []
        evts = get_events(jobs.jobs)
        # Collect candidate points adjacent to birth/death events
        while evts:
            evt = heapq.heappop(evts)
            if evt.kind == EventKind.Birth:
                cand = evt.time + 1
            else:
                cand = evt.time - 1
            if left < cand < right:
                pts.append(cand)
        if not pts:
            raise RuntimeError("No valid critical points found.")
        # print("Critical points:", pts, left, right)
        return random.choice(pts)

# @dataclass(order=True)
class EventKind(IntEnum):
    Death = 0  # 先 death，再 birth
    Birth = 1

class Event:
    __slots__ = ("time","kind","job")
    def __init__(self,  job: "Job", kind: EventKind,time: int):
        self.job  = job
        self.kind = kind
        self.time = time
        
    def __lt__(self, other: "Event"):
        if self.time != other.time:
            return self.time < other.time
        if self.kind != other.kind:
            return self.kind < other.kind  # Death < Birth
        if self.kind == EventKind.Birth:
            return self.job.death < other.job.death  # 提前结束的 birth 在前
        return False  # 两个 Death，认为一样

# def get_events(jobs: List[Job]) -> List[Event]:
#     evts: List[Event] = []
#     for j in jobs:
#         # 注意：我们的 liveness 是 (start, end) 开区间
#         evts.append(Event(j.birth, EventKind.Birth, j))
#         evts.append(Event(j.death,   EventKind.Death, j))
#     heapq.heapify(evts)
#     return evts

# def interval_graph_coloring(jobs: List[Job]) -> List[List[Job]]:
#     js = sorted(jobs, key=lambda j: j.start)
#     rows: List[List[Job]] = []
#     heap: List[Tuple[int,int]] = []  # (end,row)
#     for j in js:
#         if heap and heap[0][0] <= j.start:
#             end, rid = heapq.heappop(heap)
#             rows[rid].append(j)
#             heapq.heappush(heap, (j.end, rid))
#         else:
#             rid = len(rows)
#             rows.append([j])
#             heapq.heappush(heap, (j.end, rid))
#     return rows

def compute_max_load(jobs: List[Job]) -> int:
    evts = get_events(jobs)
    running = 0
    mx = 0
    while evts:
        e = heapq.heappop(evts)
        if e.kind == 0:
            running += e.job.size
            mx = max(mx, running)
        else:
            running -= e.job.size
    return mx


def rogue(input_inst: Instance, epsilon: float) -> Instance:
    """
    Variant of Theorem 16 first phase: partition by safety, small via c_15,
    recurse on merged instance until safe invariants break.
    """
    r, mu, h, is_safe = input_inst.get_safety_info(epsilon)
    target_size = math.floor(mu * h)
    if is_safe:
        # assumption: log2(r)^2 >= 1/epsilon
        x_s, x_l = input_inst.split_by_height(target_size)
        small_boxed = c_15(x_s, h, mu)
        merged = x_l.merge_with(small_boxed)
        return rogue(merged, epsilon)
    else:
        return input_inst


def c_15(input_inst: Instance, h: float, epsilon: float) -> Instance:
    """
    Corollary 15: bucketize and apply t_2 to each in parallel,
    then merge results.
    """
    buckets = Instance.make_buckets(input_inst, epsilon)
    res = Instance([])
    # lock = Lock()
    # sequential for clarity; can be parallelized
    for h_i, unit_jobs in buckets.items():
        assert h_i <= h
        h_param = math.floor(h / h_i)
        boxed = t_2(unit_jobs, h_param, int(h), epsilon, None)
        # with lock:
        res.merge_via_ref(boxed)
    return res

def t_2(
    input_jobs: Instance,
    h: ByteSteps,
    h_real: ByteSteps,
    epsilon: float,
    ctrl: Optional[T2Control]
) -> Instance:
    """
    Buchsbaum's Theorem 2 implementation: strip, recurse, box unresolved.
    Returns new Instance.
    """
    if ctrl is None:
        ctrl = T2Control(input_jobs)
    pts_vec = list(ctrl.critical_points)
    r_coarse, x_is = input_jobs.split_by_liveness(ctrl.critical_points)
    assert r_coarse, "Theorem 2 entered infinite loop"
    r_is = split_ris(r_coarse, pts_vec)
    res_jobs: List[Job] = []
    all_unresolved: List[Job] = []
    for r_i in r_is:
        boxed_opt, unresolved = lemma_1(r_i, h, h_real, epsilon)
        all_unresolved.extend(unresolved)
        if boxed_opt is not None:
            res_jobs.extend(boxed_opt)
    # box unresolved via interval graph coloring and gap finder
    igc_rows = interval_graph_coloring(all_unresolved)
    points_to_allocate: Set[ByteSteps] = set()
    jobs_buf: List[Job] = []
    row_count = 0
    for row in igc_rows:
        points_to_allocate |= gap_finder(row, ctrl.bounding_interval[0], ctrl.bounding_interval[1])
        row_count += 1
        jobs_buf.extend(row)
        if row_count % h == 0:
            res_jobs.append(Job.new_box(jobs_buf, h_real))
            jobs_buf = []
    if jobs_buf:
        res_jobs.append(Job.new_box(jobs_buf, h_real))
    # recurse on x_i's in parallel
    res_inst = Instance(res_jobs)
    # lock = Lock()
    for i, x_i in x_is.items():
        bi_start, bi_end = pts_vec[i], pts_vec[i+1]
        crit_pts = set([bi_start, bi_end])
        # allocate existing points
        for v in sorted(points_to_allocate):
            if bi_start < v < bi_end:
                crit_pts.add(v)
        # ensure at least one live point
        if not any(j.is_live_at(v) for j in x_i.jobs for v in crit_pts if bi_start < v < bi_end):
            crit_pts.add(T2Control.gen_crit(x_i, bi_start, bi_end))
        ctrl_i = T2Control(bounding_interval=(bi_start, bi_end), critical_points=crit_pts)
        x_i_res = t_2(x_i, h, h_real, epsilon, ctrl_i)
        # with lock:
        res_inst.merge_via_ref(x_i_res)
    return res_inst


class IndexMap:
    """
    Simple OrderedDict-like mapping where popitem(last=True) behaves like OrderedDict.
    Provides pop() to remove and return the last item.
    Also supports shift_remove by key.
    """
    def __init__(self, iterable=None):
        self._keys = []
        self._map = {}
        if iterable:
            for key, value in iterable:
                self._keys.append(key)
                self._map[key] = value

    def __len__(self):
        return len(self._keys)

    def __bool__(self):
        return bool(self._keys)

    def popitem(self):
        """Pop and return the last (key, value) pair."""
        if not self._keys:
            raise KeyError('popitem(): indexmap is empty')
        key = self._keys.pop()
        value = self._map.pop(key)
        return key, value

    def shift_remove(self, key):
        """Remove key from map, leaving other order intact."""
        if key in self._map:
            self._keys.remove(key)
            return self._map.pop(key)
        else:
            raise KeyError(f'shift_remove: key {key} not found')

    def pop(self):
        """Alias for popitem (pop last)."""
        return self.popitem()

    def items(self):
        return [(k, self._map[k]) for k in self._keys]

    def __iter__(self):
        for k in self._keys:
            yield k

    def __getitem__(self, key):
        return self._map[key]

    def __setitem__(self, key, value):
        if key not in self._map:
            self._keys.append(key)
        self._map[key] = value

    def __contains__(self, key):
        return key in self._map


def lemma_1(
    input_jobs: List[Job],
    h: int,
    h_real: int,
    e: float
) -> Tuple[Optional[List[Job]], List[Job]]:
    """
    Python translation of Rust's lemma_1:
    - input_jobs: list of Job
    - h: box-row count parameter
    - h_real: actual box height
    - e: epsilon parameter
    Returns (boxed_jobs, unresolved_jobs)
    """

    # Number of jobs in each outer strip
    outer_num = int(math.ceil(h * (1.0 / (e ** 2))))
    total_jobs = len(input_jobs)

    # Only strip if enough jobs
    if total_jobs > 2 * outer_num:
        # Build Horizontal source: sorted by death ascending (largest death last)
        hor_source = IndexMap()
        for job in sorted(input_jobs, key=lambda job: job.death):
            hor_source[job.id] = job

        # Build Vertical source: sorted by birth ascending, then reversed
        vert_source = IndexMap()
        for job in reversed(sorted(input_jobs, key=lambda job: job.birth)):
            vert_source[job.id] = job

        # Outer strips
        outer_vert = strip_cuttin(vert_source, hor_source, outer_num, True)
        outer_hor  = strip_cuttin(hor_source, vert_source, outer_num, False)

        total_jobs -= 2 * outer_num
        inner_jobs = 0
        inner_num = int(math.ceil(h * (1.0 / e)))

        inner_vert: List[List[VertStripJob]] = []
        inner_hor:  List[List[HorStripJob]]  = []

        # Inner strips loop
        while inner_jobs < total_jobs:
            vs = strip_cuttin(vert_source, hor_source, inner_num, True)
            inner_jobs += len(vs)
            inner_vert.append(vs)
            if inner_jobs >= total_jobs:
                break
            hs = strip_cuttin(hor_source, vert_source, inner_num, False)
            inner_jobs += len(hs)
            inner_hor.append(hs)

        # All source maps should be empty now
        assert len(vert_source) == 0 and len(hor_source) == 0

        # Merge inner strips into boxed jobs
        boxed = strip_boxin(inner_vert, inner_hor, h, h_real)

        # Collect unresolved outer-strip jobs
        unresolved = [vj.job for vj in outer_vert] + [hj.job for hj in outer_hor]

        return boxed, unresolved
    else:
        # Not enough jobs to strip: no boxing, all jobs unresolved
        return None, input_jobs.copy()

# def lemma_1(
#     input_jobs: List[Job],
#     h: ByteSteps,
#     h_real: ByteSteps,
#     epsilon: float
# ) -> Tuple[Optional[List[Job]], List[Job]]:
#     """
#     Implements Buchsbaum et al's Lemma 1: strip outer and inner buckets
#     and return (boxed_jobs?, unresolved_jobs).
#     """
#     outer_num = h * math.ceil(1 / epsilon**2)
#     total_jobs = len(input_jobs)
#     if total_jobs > 2 * outer_num:
#         # from indexmap import IndexMap
#         # prepare sources
#         hor = IndexMap(
#             sorted([(j.id, j) for j in input_jobs], key=lambda x: x[1].death)
#         )
#         vert = IndexMap([(j.id, j) for j in reversed(input_jobs)])
#         outer_vert = strip_cuttin(vert, hor, outer_num)
#         outer_hor = strip_cuttin(hor, vert, outer_num)
#         total_jobs -= 2 * outer_num
#         inner_num = h * math.ceil(1 / epsilon)
#         inner_vert = []
#         inner_hor = []
#         inner_jobs = 0
#         while inner_jobs < total_jobs:
#             vs = strip_cuttin(vert, hor, inner_num)
#             inner_jobs += len(vs)
#             inner_vert.append(vs)
#             if inner_jobs >= total_jobs:
#                 break
#             hs = strip_cuttin(hor, vert, inner_num)
#             inner_jobs += len(hs)
#             inner_hor.append(hs)
#         boxed = strip_boxin(inner_vert, inner_hor, h, h_real)
#         unresolved = [vj.job for vs in inner_vert for vj in vs] + [hj.job for hs in inner_hor for hj in hs]
#         return boxed, unresolved
#     else:
#         return None, input_jobs


# ---------- instance.py ----------
from typing import List, Tuple, Dict, Set
import math
# from models import Job

# Assume Job and helper functions (get_events, get_total_originals_boxed) are defined elsewhere.

def init(in_elts: List[Job]) -> List[Job]:
    """
    Initialize a JobSet, enforcing idealloc assumptions:
      - no job has zero size
      - all deaths are after births
      - valid alignment if specified
      - jobs are original (no prior boxing)
      - allocated size >= requested size
    Raises JobError on violation.
    """
    for j in in_elts:
        if j.size == 0:
            raise ("Job with 0 size found!", j)
        if j.birth >= j.death:
            raise ("Job with birth >= death found!", j)
        if j.alignment is not None and j.alignment == 0:
            raise ("Job with 0 alignment found!", j)
        if not j.is_original():
            raise ("Unoriginal job found! (non-empty contents)", j)
        if j.originals_boxed != 0:
            raise ("Unoriginal job found! (non-zero originals_boxed)", j)
        if j.size < j.req_size:
            raise ("Job with req > alloc size found!", j)
    return list(in_elts)


def split_ris(jobs: List[Job], pts: List[ByteSteps]) -> List[List[Job]]:
    """
    Recursively split jobs into R_i groups as per Theorem 2.
    pts must be sorted timepoints; len(pts) >= 3 to split around midpoint.
    """
    res: List[List[Job]] = []
    if len(pts) >= 3:
        q = len(pts) - 2
        idx_mid = math.ceil(q / 2)
        t_mid = pts[idx_mid]
        live_at, die_before, born_after = [], [], []
        for j in jobs:
            if j.is_live_at(t_mid):
                live_at.append(j)
            elif j.dies_before(t_mid):
                die_before.append(j)
            elif j.born_after(t_mid):
                born_after.append(j)
            else:
                raise RuntimeError("Unreachable partition case in split_ris")
        res.append(live_at)
        if die_before:
            res.extend(split_ris(die_before, pts[:idx_mid]))
        if born_after:
            res.extend(split_ris(born_after, pts[idx_mid+1:]))
    else:
        res.append(jobs)
    return res


def get_max_size(jobs: List[Job]) -> ByteSteps:
    """Return the maximum job size in the set."""
    return max(j.size for j in jobs)


def get_events(jobs: List[Job]) -> List[Event]:
    """Build a min-heap of birth/death events for a set of jobs."""
    evts = [Event(j, EventKind.Birth, j.birth) for j in jobs]
    evts += [Event(j, EventKind.Death, j.death) for j in jobs]
    heapq.heapify(evts)
    return evts


def get_load(jobs: List[Job]) -> ByteSteps:
    """
    Compute interval load: max total size of live jobs at any time.
    """
    running = 0
    max_load = 0
    evts = get_events(jobs)
    while evts:
        evt = heapq.heappop(evts)
        if evt.kind == EventKind.Birth:
            running += evt.job.size
            max_load = max(max_load, running)
        else:
            running -= evt.job.size
    return max_load


def get_total_originals_boxed(jobs: List[Job]) -> int:
    """Sum of originals_boxed across all jobs."""
    return sum(j.originals_boxed for j in jobs)


def interval_graph_coloring(jobs: List[Job]) -> List[List[Job]]:
    """
    Perform interval graph coloring (IGC) to assign each job to a row.
    Returns a list of rows, each row a list of jobs.
    """
    res: List[List[Job]] = []
    free_rows = [0]
    heapq.heapify(free_rows)
    max_row = 0
    cheatsheet: Dict[int, ByteSteps] = {}
    evts = get_events(jobs)
    while evts:
        evt = heapq.heappop(evts)
        if evt.kind == EventKind.Birth:
            row = heapq.heappop(free_rows)
            cheatsheet[evt.job.id] = row
            if row < len(res):
                res[row].append(evt.job)
            else:
                assert row == len(res)
                res.append([evt.job])
            if not free_rows:
                max_row += 1
                heapq.heappush(free_rows, max_row)
        else:
            row = cheatsheet.pop(evt.job.id)
            heapq.heappush(free_rows, row)
    return res


def gap_finder(row_jobs: List[Job], alpha: ByteSteps, omega: ByteSteps) -> Set[ByteSteps]:
    """
    Find gaps between jobs in a single IGC row within [alpha, omega].
    Returns a set of gap endpoints.
    """
    res: Set[ByteSteps] = set()
    evts = get_events(row_jobs)
    gap_start: Optional[ByteSteps] = alpha
    while evts:
        evt = heapq.heappop(evts)
        if evt.kind == EventKind.Birth and gap_start is not None and gap_start < evt.time:
            res.update({gap_start, evt.time})
            gap_start = None
        elif evt.kind == EventKind.Death:
            gap_start = evt.time
    if gap_start is not None and gap_start < omega:
        res.add(gap_start)
    return res

def init_rogue(input_inst: Instance, small: float, big: float) -> Tuple[float, Instance]:
    """
    Calls `rogue` for a variety of ε-values, returning the one
    which results in the smallest min/max height ratio, along with
    its almost-converged Instance.
    """
    e = small
    min_r = float('inf')
    best_e = e
    tries_left = 3
    best = input_inst
    _test = input_inst
    while True:
        if tries_left > 0:
            _test = rogue(input_inst, e)
            r, _, _, _ = _test.get_safety_info(e)
            if r < min_r:
                min_r = r
                best_e = e
                best = _test
                tries_left = 3
            else:
                tries_left -= 1
            e += (big - e) * 0.01
        else:
            return best_e, best


def placement_is_valid(
    ig: Dict[int, List[Job]],
    reg: Any  # PlacedJobRegistry-like mapping from job ID to Job
) -> bool:
    """
    Verify that no two interfering jobs overlap in placement.
    `ig` maps job IDs to lists of interfering jobs.
    `reg` provides `get(id)` returning a placed Job with
    `.offset.get()` and `.next_avail_offset()` methods.
    """
    for job_id, interferers in ig.items():
        this_job = reg.get(job_id)
        this_start = this_job.offset
        this_end = this_job.next_avail_offset() - 1
        for other in interferers:
            that_start = other.offset
            that_end = other.next_avail_offset() - 1
            # no overlap if other's start is after this job's end
            if that_start > this_end:
                continue
            # overlap detected
            if that_start >= this_start or that_end >= this_start:
                print(f"{this_job} conflicts with {other}!")
                return False
    return True

# Define UnboxCtrl for get_loose_placement
class UnboxCtrl:
    """
    Control states for loose placement unboxing.
    """
    def __init__(self, kind: str, row_height: Optional[int] = None):
        self.kind = kind
        self.row_height = row_height

    @classmethod
    def SameSizes(cls, row_height: int) -> 'UnboxCtrl':
        return cls('SameSizes', row_height)

    @classmethod
    def NonOverlapping(cls) -> 'UnboxCtrl':
        return cls('NonOverlapping')

    @classmethod
    def Unknown(cls) -> 'UnboxCtrl':
        return cls('Unknown')

# LoosePlacement is a min-heap of PlacedJob
LoosePlacement = List[PlacedJob]
PlacedJobRegistry = Dict[int, PlacedJob]
InterferenceGraph = Dict[int, List[PlacedJob]]
JobSet = List[Job]

# Monkey-patch Instance.place

def instance_place(self: Instance,
                   ig: Tuple[InterferenceGraph, PlacedJobRegistry],
                   iters_done: int,
                   makespan_lim: int,
                   dumb_id: int,
                   start_addr: int) -> int:
    """
    Unbox and tighten placement, returning makespan.
    """
    row_size = self.jobs[0].size  # assumes non-empty
    loose = get_loose_placement(
        list(self.jobs),
        0,
        UnboxCtrl.SameSizes(row_size),
        ig[1],
        dumb_id
    )
    return do_best_fit(loose, ig[0], iters_done, makespan_lim, True, start_addr)
Instance.place = instance_place


def get_loose_placement(
    jobs: JobSet,
    start_offset: int,
    control_state: UnboxCtrl,
    ig: PlacedJobRegistry,
    dumb_id: int
) -> LoosePlacement:
    """
    Builds an initial loose placement of jobs as PlacedJob heap.
    """
    res: LoosePlacement = []
    # single job case
    if len(jobs) == 1:
        only = jobs[0]
        if only.is_original():
            if only.id != dumb_id:
                to_put = ig[only.id]
                to_put.offset = start_offset
                res.append(to_put)
        else:
            # unwrap box
            contents = only.contents or []
            res.extend(get_loose_placement(contents,
                                           start_offset,
                                           UnboxCtrl.Unknown(),
                                           ig,
                                           dumb_id))
        return res
    # multi-job
    kind = control_state.kind
    if kind == 'SameSizes':
        row_height = control_state.row_height
        for row in interval_graph_coloring(jobs):
            res.extend(get_loose_placement(row,
                                           start_offset,
                                           UnboxCtrl.NonOverlapping(),
                                           ig,
                                           dumb_id))
            start_offset += row_height or 0
    elif kind == 'NonOverlapping':
        for j in jobs:
            if j.is_original():
                if j.id != dumb_id:
                    to_put = ig[j.id]
                    to_put.offset = start_offset
                    res.append(to_put)
            else:
                contents = j.contents or []
                res.extend(get_loose_placement(contents,
                                               start_offset,
                                               UnboxCtrl.Unknown(),
                                               ig,
                                               dumb_id))
    else:  # Unknown
        size_probe = jobs[0].size
        if all(j.size == size_probe for j in jobs[1:]):
            res.extend(get_loose_placement(jobs,
                                           start_offset,
                                           UnboxCtrl.SameSizes(size_probe),
                                           ig,
                                           dumb_id))
        else:
            # test non-overlap via events
            evts = get_events(jobs)
            last_birth = False
            non_overlap = True
            while evts:
                e = heapq.heappop(evts)
                if e.kind == EventKind.Birth:
                    if last_birth:
                        non_overlap = False
                        break
                    last_birth = True
                else:
                    last_birth = False
            if non_overlap:
                res.extend(get_loose_placement(jobs,
                                               start_offset,
                                               UnboxCtrl.NonOverlapping(),
                                               ig,
                                               dumb_id))
            else:
                # bucket by size
                size_buckets: Dict[int, JobSet] = {}
                for j in jobs:
                    size_buckets.setdefault(j.size, []).append(j)
                for row_height, bucket in size_buckets.items():
                    for row in interval_graph_coloring(bucket):
                        res.extend(get_loose_placement(row,
                                                       start_offset,
                                                       UnboxCtrl.NonOverlapping(),
                                                       ig,
                                                       dumb_id))
                        start_offset += row_height
    return res


def do_best_fit(
    loose: LoosePlacement,
    ig: InterferenceGraph,
    iters_done: int,
    makespan_lim: int,
    first_fit: bool,
    start_addr: int
) -> int:
    """
    Best/first-fit placement of PlacedJob heap; returns makespan or MAX if limit exceeded.
    """
    max_address = 0
    heapq.heapify(loose)
    while loose:
        to_squeeze = heapq.heappop(loose)
        min_gap = to_squeeze.descr.size
        offset_runner = 0
        smallest_gap = math.inf
        best_offset: Optional[int] = None
        # interfering jobs that have been placed in this iteration
        placed = ig[to_squeeze.descr.id]
        # filter by times_squeezed
        placed = [pj for pj in placed if pj.times_squeezed == iters_done + 1]
        # sort by offset ascending
        placed.sort(key=lambda pj: pj.offset)
        for pj in placed:
            njo = pj.offset
            test_off = to_squeeze.get_corrected_offset(start_addr, offset_runner)
            if njo > test_off and njo - test_off >= min_gap:
                if first_fit:
                    best_offset = test_off
                    break
                else:
                    gap = njo - test_off
                    if gap < smallest_gap:
                        smallest_gap = gap
                        best_offset = test_off
            offset_runner = max(offset_runner, max(test_off, pj.next_avail_offset()))
        if best_offset is not None:
            to_squeeze.offset = best_offset
        else:
            to_squeeze.offset = offset_runner
        to_squeeze.times_squeezed = iters_done + 1
        cand_end = to_squeeze.next_avail_offset()
        if cand_end > max_address:
            max_address = cand_end
            if max_address > makespan_lim:
                return float('inf')  # exceed
    return max_address

# ---------- analyze.py ----------
from typing import List, Dict, Set, NamedTuple, Optional
# from helpers import get_events, compute_max_load
# from instance import Instance
# from models import Job

class AnalysisResult(NamedTuple):
    kind: str
    jobs: List[Job]
    igraph: Optional[Dict[int,Set[int]]] = None
    ctrl:   Optional[Dict]             = None


# PreludeAnalysis results
t = Tuple
PreludeResult = Union['NoOverlap','SameSizes','NeedsBA']
@dataclass
class NoOverlap:
    jobs: List[Job]

@dataclass
class SameSizes:
    jobs: List[Job]
    registry: Dict[int,PlacedJob]

@dataclass
class NeedsBA:
    input_inst:       Instance
    pre_boxed:   Instance
    epsilon:     float
    to_box:      int
    real_load:   ByteSteps
    dummy:       Optional[Job]
    ig:          InterferenceGraph
    reg:         PlacedJobRegistry
    mu_lim:      float
    best_opt:    ByteSteps
    hardness:    Tuple[float, float, float]   # (h_hard, conflict_hard, death_hard)

def prelude_analysis(jobs: List[Job], start_addr: ByteSteps) -> PreludeResult:
    last_evt_was_birth = False
    overlap_exists = False
    same_sizes = False
    running_load = 0
    max_load = 0
    sizes: Set[ByteSteps] = set()
    # build interference graph
    ig: Dict[int,List[PlacedJob]] = {}
    registry: Dict[int,PlacedJob] = {}
    live: Dict[int,PlacedJob] = {}
    # BA config
    h_min = sys.maxsize
    h_max = 0
    max_death = 0
    max_id = 0
    # hardness
    sizes_sum = 0
    deaths_sum = 0

    # process events in time order
    evts = get_events(jobs)
    while evts:
        e =heapq.heappop(evts) # pop min-time event
        if e.kind == EventKind.Birth:
            # update h_min / h_max / id
            h = e.job.size
            h_min = min(h_min, h)
            h_max = max(h_max, h)
            max_id = max(max_id, e.job.id)
            sizes_sum += h

            # update running + max load
            running_load += h
            max_load = max(max_load, running_load)

            # track sizes
            sizes.add(h)

            # build interference graph
            # init adjacency for this job
            ig[e.job.id] = [pj for pj in live.values()]
            new_pj = PlacedJob(e.job)  # wrap job
            registry[e.job.id] = new_pj
            # add this job to others' lists
            for other in live.values():
                assert other.overlaps_with(new_pj)
                ig[other.descr.id].append(new_pj)
            # mark as live
            live[e.job.id] = new_pj

            # detect first time overlap
            if last_evt_was_birth and not overlap_exists and not same_sizes:
                overlap_exists = True
                if len(sizes) == 1:
                    probe = next(iter(sizes))
                    if all(j.size == probe for j in jobs):
                        same_sizes = True
            last_evt_was_birth = True

        else:  # e.kind == EventKind.Death
            # update running load
            running_load -= e.job.size
            last_evt_was_birth = False if not overlap_exists else last_evt_was_birth
            # remove from live
            live.pop(e.job.id, None)
            # stats
            deaths_sum += e.job.death
            max_death = max(max_death, e.job.death)

    # quick return cases
    if not overlap_exists:
        # print(f"Prelude time: {(time.time()-start_time)*1e6:.0f}μs")
        return NoOverlap(jobs)
    if same_sizes:
        # print(f"Prelude time: {(time.time()-start_time)*1e6:.0f}μs")
        return SameSizes(jobs, ig, registry)

    # fallback heuristic: size-life ordering + one best-fit
    ordered = sorted(registry.values(),
                     key=lambda pj: (-pj.descr.size, -pj.descr.lifetime()))
    # assign symbolic offsets
    for i, pj in enumerate(ordered):
        pj.offset = i
    best_opt = do_best_fit(ordered, ig, 0, float('inf'), True, start_addr)

    # compute BA parameters
    r = h_max / h_min
    lgr = math.log2(r)
    lg2r = lgr * lgr
    small_end = (lg2r**7 / r)**(1/6)
    mu_lim = (math.sqrt(5) - 1) / 2
    big_end = mu_lim * lg2r

    to_box = len(jobs)
    dummy = None
    real_load = max_load

    # instance characterization: hardness metrics
    h_mean = sizes_sum / to_box
    death_mean = deaths_sum / to_box
    h_var = sum((j.size - h_mean)**2 for j in jobs) / to_box
    d_var = sum((j.death - death_mean)**2 for j in jobs) / to_box
    h_hardness = math.sqrt(h_var) / h_mean
    death_hardness = math.sqrt(d_var) / death_mean
    double_conflicts = sum(len(lst) for lst in ig.values())
    num_pairs = to_box * (to_box - 1) / 2
    conflict_hardness = (double_conflicts/2) / num_pairs

    # possibly insert dummy job
    if small_end >= big_end:
        h_max = math.ceil(2216.54 * h_min)
        dummy_job = Job(
            size=h_max, birth=0, death=max_death,
            req_size=h_max, alignment=None,
            contents=None, originals_boxed=0, id=max_id+1
        )
        jobs.append(dummy_job)
        to_box += 1
        max_load += h_max
        dummy = dummy_job

    # prepare for BA
    instance = Instance(jobs)
    instance.info.set_load(max_load)
    instance.info.set_heights((h_min, h_max))
    eps, pre_boxed = init_rogue(instance, small_end, big_end)

    # print(f"Prelude time: {(time.time()-start_time)*1e6:.0f}μs")
    return NeedsBA(
        input_inst=instance,
        pre_boxed=pre_boxed,
        epsilon=eps,
        to_box=to_box,
        real_load=real_load,
        dummy=dummy,
        ig=ig,
        reg=registry,
        mu_lim=mu_lim,
        best_opt=best_opt,
        hardness=(h_hardness, conflict_hardness, death_hardness)
    )


def idealloc(
    original_input: List['Job'],
    worst_case_frag: float,
    start_address: int,
    max_lives: int
) -> Tuple[Dict[int, PlacedJob], int]:
    total_start = time.time()

    # Analyze trivial cases
    analysis_result = prelude_analysis(original_input, start_address)
    if isinstance(analysis_result, NoOverlap):
        # Handle the non-overlapping case
        target_load = get_load(analysis_result.jobs)
        best_opt = get_max_size(analysis_result.jobs)
        placement = {
            placed.descr.id: PlacedJob(placed.descr)
            for placed in analysis_result.jobs
        }
    elif isinstance(analysis_result, SameSizes):
        # Handle same sizes case
        target_load = get_load(analysis_result.jobs)
        best_opt = get_max_size(analysis_result.jobs)
        placement = {
            placed.descr.id: PlacedJob(placed.descr)
            for placed in analysis_result.reg.values()
        }
        loose = []
        for row_idx, igc_row in enumerate(interval_graph_coloring(analysis_result.jobs)):
            for job in igc_row:
                semi_placed = analysis_result.reg.get(job.id)
                semi_placed.offset = row_idx * job.size
                loose.append(semi_placed)
        best_opt = do_best_fit(loose, analysis_result.ig, 0, float('inf'), False, start_address)
    elif isinstance(analysis_result, NeedsBA):
        # Handle the complex case with best fit and adjustments
        heuristic_opt = analysis_result.best_opt
        lives_left = max_lives
        total_iters = 1
        target_opt = int(analysis_result.real_load * worst_case_frag)
        dumb_id = analysis_result.dummy.id if analysis_result.dummy else 2**31 - 1

        final_placement = {
            placed.descr.id: PlacedJob(placed.descr)
            for placed in analysis_result.reg.values()
        }
        ig_reg = (analysis_result.ig, analysis_result.reg)
        # Ensure placement is valid
        assert placement_is_valid(ig_reg[0], ig_reg[1])

        # Initializations related to C15
        pre_boxed = analysis_result.pre_boxed
        _, mu, _, _ = pre_boxed.get_safety_info(analysis_result.epsilon)
        if mu > analysis_result.mu_lim:
            mu = 0.99 * analysis_result.mu_lim
        _, h_max = analysis_result.input_inst.min_max_height()
        final_h = h_max / mu

        while lives_left > 0 and analysis_result.best_opt > target_opt:
            boxed = c_15(pre_boxed, final_h, mu)
            current_opt = boxed.place(ig_reg, total_iters, analysis_result.best_opt, dumb_id, start_address)

            if current_opt < analysis_result.best_opt:
                assert placement_is_valid(ig_reg[0], ig_reg[1])
                analysis_result.best_opt = current_opt
                print("Beating heuristic by {} bytes! ({total_iters} iterations)", heuristic_opt - analysis_result.best_opt)

                final_placement = {
                pj.descr.id: PlacedJob(descr=pj.descr, offset=pj.offset)
                for pj in ig_reg[1].values()
                }

            total_iters += 1
            lives_left -= 1
            if lives_left > 0 and analysis_result.best_opt > target_opt:
                pre_boxed = rogue(analysis_result.input_inst.clone(), analysis_result.epsilon)
            else:
                break
        num_buffers = len(ig_reg[1])
        hardness       = analysis_result.hardness
        best_opt = analysis_result.best_opt
        target_load = analysis_result.real_load
        
        print(f"\n Buffers treated:\t{num_buffers}"
            f"\nHeights hardness:\t{hardness[0]*100:.2f}%"
            f"\nConflicts hardness:\t{hardness[1]*100:.2f}%"
            f"\nDeaths hardness:\t{hardness[2]*100:.2f}%"
            f"\nCompound hardness:\t{(1+hardness[0])*(1+hardness[1])*(1+hardness[2]):.2f}"
            f"\n{heuristic_opt - best_opt} fewer bytes than heuristic.\n")
        print(f"Total allocation time: {time.time() - total_start} seconds")
        print(f"Makespan: {analysis_result.best_opt} bytes")
        print(
            f"Makespan:\t{best_opt} bytes\n"
            f"LOAD:\t\t{target_load} bytes\n"
            f"Fragmentation:\t{(best_opt - target_load) / target_load * 100:.2f}%"
        )
        return final_placement, analysis_result.best_opt


# ---------- boxing.py ----------
from typing import List, Dict
import math
# from models import Job
# from helpers import interval_graph_coloring
# from instance import Instance


def lemma1_unit_boxing(jobs: List[Job], H:int, eps:float):
    if H<=0: return [], jobs[:]
    sj = sorted(jobs, key=lambda j: j.end, reverse=True)
    boxed=[]
    for i in range(0,len(sj),H):
        grp = sj[i:i+H]
        if len(grp)==H:
            st=min(j.start for j in grp)
            en=max(j.end  for j in grp)
            boxed.append(Job(0,H,st,en,contents=list(grp)))
    unresolved = sj[(len(sj)//H)*H:]
    return boxed, unresolved


def theorem2_boxing_unit(jobs: List[Job], H: int, eps: float) -> List[Job]:
    """
    根据 Theorem 2，使用 Lemma 1 和区间图着色对 jobs 列表进行打包。
    - jobs: 待打包的区间列表
    - H: 最大高度
    - eps: Lemma1 中的误差参数
    返回：打包后的 Job 列表，每个 Job 的高度区间均为 [0, H]。
    """
    allb: List[Job] = []
    stack: List[List[Job]] = [jobs]

    while stack:
        X = stack.pop()
        if not X:
            continue
        # 如果数量不超过 H，直接打成一个 box
        if len(X) <= H:
            st = min(j.start for j in X)
            en = max(j.end for j in X)
            allb.append(Job(0, H, st, en, contents=list(X)))
            continue

        # 计算分割点 t
        starts = sorted(j.start for j in X)
        ends = sorted(j.end for j in X)
        if len(set(starts)) == 1:
            # 所有 start 相同时，用 end 的中位数做 t
            t = (starts[0] + ends[len(ends)//2]) / 2
        else:
            t = starts[len(starts)//2]

        # 按 t 划分
        L = [j for j in X if j.end <= t]
        G = [j for j in X if j.start >= t]
        R = [j for j in X if j.start < t < j.end]

        # 如果划分未缩小子问题，则退化到简单二分
        if len(L) + len(R) + len(G) != len(X) or (not L and not G):
            mid = len(X) // 2
            sorted_by_start = sorted(X, key=lambda j: j.start)
            L = sorted_by_start[:mid]
            G = sorted_by_start[mid:]
            R = []
            t = (starts[0] + ends[-1]) / 2

        # 对重叠组 R 应用 Lemma1
        bs, un = lemma1_unit_boxing(R, H, eps)
        # 已打包的 bs 直接加入
        for b in bs:
            allb.append(Job(0, H, b.start, b.end, contents=b.contents))

        # 对 lemma1 剩余的 un 做图着色
        rows = interval_graph_coloring(un)
        for row in rows:
            st = min(j.start for j in row)
            en = max(j.end for j in row)
            allb.append(Job(0, H, st, en, contents=list(row)))

        # 递归处理左右两侧子问题
        stack.append(L)
        stack.append(G)

    return allb


def corollary15_discretize_and_box(jobs: List[Job], H:int, eps:float) -> List[Job]:
    groups:Dict[int,List[Job]]={}
    for j in jobs:
        i=math.ceil(math.log(j.size,1+eps))
        hr=int((1+eps)**i)
        groups.setdefault(hr,[]).append(j)
    allb=[]
    for hr,grp in groups.items():
        for j in grp: j.size=1
        bs=theorem2_boxing_unit(grp,max(1,H//hr),eps)
        for b in bs: b.size=hr
        allb+=bs
    return allb


def theorem16_recursive_box(jobs: List[Job], eps:float=0.05) -> List[Job]:
    X=jobs[:]
    hmax=max(j.size for j in X)
    while True:
        hmin=min(j.size for j in X)
        r=hmax/hmin if hmin>0 else 1.0
        lg2r=math.log2(r)**2 if r>1 else 1.0
        mu=eps/lg2r if r>1 else eps
        H=max(1,math.ceil(mu**5*hmax/lg2r))
        Xs=[j for j in X if j.size<=mu*H]
        Xl=[j for j in X if j.size> mu*H]
        if not Xs: break
        Bs=corollary15_discretize_and_box(Xs,H,mu)
        X=Bs+Xl
        if math.log2(hmax/min(j.size for j in X))**2<1/eps:
            break
    return corollary15_discretize_and_box(X,H,eps)


def unbox_all(jobs: List[Job], base_offset:int=0) -> None:
    if not jobs: return
    if any(j.contents for j in jobs):
        sizes={j.size for j in jobs}
        if len(sizes)==1:
            rows=interval_graph_coloring(jobs)
            off=base_offset
            for row in rows:
                for b in row:
                    b.offset=off; off+=b.size
                for b in row:
                    unbox_all(b.contents,b.offset)
        else:
            from placement import first_fit_place
            first_fit_place(jobs,base_offset)
            for b in jobs:
                unbox_all(b.contents,b.offset)
    else:
        from placement import first_fit_place
        first_fit_place(jobs,base_offset)

# ---------- placement.py ----------
from typing import List, Dict
import heapq




# ---------- cli.py ----------
import argparse, csv
# from models import Job
# from analyze import prelude_analysis
# from boxing import theorem16_recursive_box, unbox_all
# from helpers import compute_max_load
# from placement import do_best_fit


def read_csv(path:str):
    jobs=[]
    with open(path) as f:
        rdr=csv.DictReader(f)
        for r in rdr:
            jobs.append(Job(int(r['lower']),int(r['upper'])+2,int(r['size']), int(r['size']), None, None, 0, int(r['id'])))
    return jobs

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('input_csv')
    p.add_argument('--frag',type=float,default=1.05)
    args=p.parse_args()
    jobs=read_csv(args.input_csv)
    ar=idealloc(jobs,1, 0, 1)
    
    # if ar.kind=='no_overlap':
    #     for j in ar.jobs: print(j.id,0)
    # elif ar.kind=='same_sizes':
    #     # 最优 IGC + squeeze
    #     from helpers import interval_graph_coloring
    #     rows=interval_graph_coloring(ar.jobs)
    #     off=0
    #     for row in rows:
    #         for j in row:
    #             j.offset=off
    #         off+=row[0].size
    #     print(off)
    # else:
    #     boxes=theorem16_recursive_box(jobs,0.05)
    #     unbox_all(boxes,0)
    #     limit=compute_max_load(jobs)
    #     # 把最终 loose 用列表替代 priority queue
    #     loose = sorted(jobs, key=lambda j: j.offset)
    #     import heapq
    #     heapq.heapify(loose)
    #     final=do_best_fit(loose,ar.igraph,0,limit,True,0)
    #     print("Makespan=", final)
