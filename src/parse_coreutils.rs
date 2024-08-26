use chrono::{DateTime, Datelike, Duration, Local, NaiveDateTime, TimeZone, Timelike, Weekday};

use crate::{parse_weekday, ParseDateTimeError};

type Result<T> = std::result::Result<T, ParseDateTimeError>;

use regex::Regex;

struct RegexParser {
    regex: Regex,
}

impl RegexParser {
    fn new(input: &str) -> Result<RegexParser> {
        Ok(RegexParser {
            regex: Regex::new(input)?,
        })
    }

    fn action<'a, T, const N: usize>(
        self,
        map: impl Fn([&'a str; N]) -> Result<T>,
    ) -> impl Fn(&'a str) -> Result<T> {
        move |token: &str| {
            self.regex
                .captures(token)
                .ok_or(ParseDateTimeError::InvalidInput)
                .and_then(|c| map(c.extract::<N>().1))
        }
    }
}

#[derive(Default, Debug)]
struct ParseState {
    year: Option<i32>,
    month: Option<i32>,
    day: Option<i32>,
    weekday: Option<Weekday>,
    relatives: Vec<Duration>,
    hour: Option<i32>,
    minute: Option<i32>,
    second: Option<i32>,
}

impl ParseState {
    fn set_by_heuristics(&mut self, val: i32) {
        if self.year.is_none() && (-3000..=3000).contains(&val) {
            self.year = Some(val)
        } else if self.month.is_none() && (1..=12).contains(&val) {
            self.month = Some(val)
        } else if self.day.is_none() && (1..=31).contains(&val) {
            self.day = Some(val)
        } else if self.hour.is_none() && (1..=24).contains(&val) {
            self.hour = Some(val)
        } else if self.minute.is_none() && (1..=60).contains(&val) {
            self.minute = Some(val)
        } else if self.second.is_none() && (1..=60).contains(&val) {
            self.second = Some(val)
        } else {
            self.relatives.push(Duration::hours(val.into()))
        }
    }

    fn ymd(&self, d: DateTime<Local>) -> (i32, i32, i32) {
        (
            self.year.unwrap_or(d.year()),
            self.month.unwrap_or(d.month() as i32),
            self.day.unwrap_or(d.day() as i32),
        )
    }

    fn hms(&self, d: DateTime<Local>) -> (i32, i32, i32) {
        (
            self.hour.unwrap_or(d.hour() as i32),
            self.minute.unwrap_or(d.minute() as i32),
            self.second.unwrap_or(d.second() as i32),
        )
    }
}

pub fn parse(mut d: DateTime<Local>, input: &str) -> Result<DateTime<Local>> {
    let mut parse_state = ParseState::default();
    let parse_weekday = parse_weekday::parse_weekday;
    let parse_i32 = RegexParser::new(r"^\+?(\d{1,9})$")?.action(|[n]| {
        n.parse::<i32>()
            .map_err(|_| ParseDateTimeError::InvalidInput)
    });
    let parse_epoch = RegexParser::new(r"^@(\d+)$")?.action(|[n]| {
        n.parse::<i64>()
            .map_err(|_| ParseDateTimeError::InvalidInput)
    });
    let parse_mmddhhmmyyyy = RegexParser::new(r"^(\d{2})(\d{2})(\d{2})(\d{2})(\d{4})$")?.action(
        |[mm, dd, hh, mm_, yyyy]| {
            Ok((
                mm.parse::<i32>().unwrap(),
                dd.parse::<i32>().unwrap(),
                hh.parse::<i32>().unwrap(),
                mm_.parse::<i32>().unwrap(),
                yyyy.parse::<i32>().unwrap(),
            ))
        },
    );
    let parse_mmddhhmm =
        RegexParser::new(r"^(\d{2})(\d{2})(\d{2})(\d{2})$")?.action(|[mm, dd, hh, mm_]| {
            Ok((
                mm.parse::<i32>().unwrap(),
                dd.parse::<i32>().unwrap(),
                hh.parse::<i32>().unwrap(),
                mm_.parse::<i32>().unwrap(),
            ))
        });
    let parse_ymd = RegexParser::new(r"^(\d{4})-(\d{2})-(\d{2})$")?.action(|[y, m, d]| {
        Ok((
            y.parse::<i32>().unwrap(),
            m.parse::<i32>().unwrap(),
            d.parse::<i32>().unwrap(),
        ))
    });
    let parse_ymd2 = RegexParser::new(r"^(\d{4})(\d{2})(\d{2})$")?.action(|[y, m, d]| {
        Ok((
            y.parse::<i32>().unwrap(),
            m.parse::<i32>().unwrap(),
            d.parse::<i32>().unwrap(),
        ))
    });
    let parse_hms = RegexParser::new(r"^(\d{2}):(\d{2}):(\d{2})$")?.action(|[h, m, s]| {
        Ok((
            h.parse::<i32>().unwrap(),
            m.parse::<i32>().unwrap(),
            s.parse::<i32>().unwrap(),
        ))
    });
    let parse_hm = RegexParser::new(r"^(\d{2}):(\d{2})$")?
        .action(|[h, m]| Ok((h.parse::<i32>().unwrap(), m.parse::<i32>().unwrap(), 0)));
    let parse_month = RegexParser::new(r"^(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dez)$")?
        .action(|[m]| match m {
            "Jan" => Ok(1),
            "Feb" => Ok(2),
            "Mar" => Ok(3),
            "Apr" => Ok(4),
            "May" => Ok(5),
            "Jun" => Ok(6),
            "Jul" => Ok(7),
            "Aug" => Ok(8),
            "Sep" => Ok(9),
            "Oct" => Ok(10),
            "Nov" => Ok(11),
            "Dez" => Ok(12),
            _ => unreachable!(),
        });
    let parse_dateunit = RegexParser::new(r"^(day|hour|minute|second|month|year)s?$")?
        .action(|[dateunit]| Ok(dateunit));

    let mut iter = input.split_whitespace().peekable();
    while let Some(token) = iter.next() {
        if let (None, Ok((mm, dd, hh, mm_, yyyy))) = (parse_state.hour, parse_mmddhhmmyyyy(token)) {
            parse_state.hour = Some(hh);
            parse_state.minute = Some(mm_);
            parse_state.month = Some(mm);
            parse_state.day = Some(dd);
            parse_state.year = Some(yyyy);
        } else if let (None, Ok((mm, dd, hh, mm_))) = (parse_state.hour, parse_mmddhhmm(token)) {
            parse_state.hour = Some(hh);
            parse_state.minute = Some(mm_);
            parse_state.month = Some(mm);
            parse_state.day = Some(dd);
        } else if let (None, Ok(ts)) = (parse_state.minute, parse_epoch(token)) {
            let d = NaiveDateTime::from_timestamp_opt(ts, 0).unwrap();
            parse_state.year = Some(d.year());
            parse_state.month = Some(d.month() as i32);
            parse_state.day = Some(d.day() as i32);
            parse_state.hour = Some(d.hour() as i32);
            parse_state.minute = Some(d.minute() as i32);
            parse_state.second = Some(d.second() as i32);
        } else if let (None, Ok((y, m, d))) = (
            parse_state.year,
            parse_ymd(token).or_else(|_| parse_ymd2(token)),
        ) {
            parse_state.year = Some(y);
            parse_state.month = Some(m);
            parse_state.day = Some(d);
        } else if let (None, Ok((h, m, s))) = (
            parse_state.hour,
            parse_hms(token).or_else(|_| parse_hm(token)),
        ) {
            parse_state.hour = Some(h);
            parse_state.minute = Some(m);
            parse_state.second = Some(s);
        } else if let (None, Ok(m)) = (parse_state.month, parse_month(token)) {
            parse_state.month = Some(m);
            if let Some(next_tk) = iter.peek() {
                if let Ok(day) = parse_i32(next_tk) {
                    if (1..=31).contains(&day) {
                        parse_state.day = Some(day);
                        iter.next(); // consume the token
                    }
                }
            }
        } else if let (None, Some(w)) = (parse_state.weekday, parse_weekday(token)) {
            parse_state.weekday = Some(w)
        } else if let Ok(num) = parse_i32(token) {
            let nxt_token = iter.peek().unwrap_or(&"hour");
            if let Ok(dateunit) = parse_dateunit(nxt_token) {
                let dateunit = match dateunit {
                    "year" => Duration::days(num as i64 * 364),
                    "month" => Duration::days(num as i64 * 30),
                    "day" => Duration::days(num as i64),
                    "hour" => Duration::hours(num as i64),
                    "minute" => Duration::minutes(num as i64),
                    "second" => Duration::seconds(num as i64),
                    _ => unreachable!(),
                };
                parse_state.relatives.push(dateunit);
                iter.next(); // consume the token
            } else {
                parse_state.set_by_heuristics(num);
            }
        }
    }

    let (yea, mon, day) = parse_state.ymd(d);
    let (hor, min, seg) = parse_state.hms(d);
    d = Local
        .with_ymd_and_hms(
            yea, mon as u32, day as u32, hor as u32, min as u32, seg as u32,
        )
        .unwrap();
    for duration in parse_state.relatives {
        d += duration
    }

    Ok(d)
}
