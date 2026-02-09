package it.unisa.uniclass.testing.unit.orari.model;

import it.unisa.uniclass.orari.model.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Nested;

import java.sql.Time;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test d'unità completi per la classe Lezione.
 * Verifica costruttori, getter, setter, relazioni JPA e metodi di utilità.
 */
@DisplayName("Test per la classe Lezione")
public class LezioneTest {

    private Lezione lezione;

    @BeforeEach
    void setUp() {
        lezione = new Lezione();
    }

    @Nested
    @DisplayName("Test dei Costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore di default crea un'istanza valida")
        void testCostruttoreDefault() {
            Lezione lezTest = new Lezione();
            assertNotNull(lezTest);
            assertNull(lezTest.getId());
            assertNull(lezTest.getOraInizio());
            assertNull(lezTest.getOraFine());
            assertNull(lezTest.getGiorno());
            assertNull(lezTest.getCorso());
            assertNull(lezTest.getResto());
            assertNull(lezTest.getAula());
            assertNotNull(lezTest.getDocenti());
            assertTrue(lezTest.getDocenti().isEmpty());
            assertEquals(0, lezTest.getSemestre());
        }

        @Test
        @DisplayName("Costruttore con parametri inizializza correttamente")
        void testCostruttoreConParametri() {
            int semestre = 1;
            Time oraInizio = Time.valueOf("09:00:00");
            Time oraFine = Time.valueOf("11:00:00");
            Giorno giorno = Giorno.LUNEDI;
            Resto resto = new Resto();
            Corso corso = new Corso("Programmazione");
            Aula aula = new Aula(1, "Edificio A", "Aula 101");

            Lezione lezTest = new Lezione(semestre, oraInizio, oraFine, giorno, resto, corso, aula);

            assertNotNull(lezTest);
            assertEquals(semestre, lezTest.getSemestre());
            assertEquals(oraInizio, lezTest.getOraInizio());
            assertEquals(oraFine, lezTest.getOraFine());
            assertEquals(giorno, lezTest.getGiorno());
            assertEquals(resto, lezTest.getResto());
            assertEquals(corso, lezTest.getCorso());
            assertEquals(aula, lezTest.getAula());
            assertNotNull(lezTest.getDocenti());
            assertTrue(lezTest.getDocenti().isEmpty());
        }

        @Test
        @DisplayName("Costruttore con parametri null")
        void testCostruttoreConParametriNull() {
            Lezione lezTest = new Lezione(1, null, null, null, null, null, null);

            assertNotNull(lezTest);
            assertEquals(1, lezTest.getSemestre());
            assertNull(lezTest.getOraInizio());
            assertNull(lezTest.getOraFine());
            assertNull(lezTest.getGiorno());
            assertNull(lezTest.getResto());
            assertNull(lezTest.getCorso());
            assertNull(lezTest.getAula());
        }

        @Test
        @DisplayName("Costruttore con semestre 2")
        void testCostruttoreConSemestre2() {
            Lezione lezTest = new Lezione(2, Time.valueOf("14:00:00"), Time.valueOf("16:00:00"), Giorno.MARTEDI, new Resto(), new Corso(), new Aula());

            assertNotNull(lezTest);
            assertEquals(2, lezTest.getSemestre());
        }

        @Test
        @DisplayName("Costruttore con tutti i giorni della settimana")
        void testCostruttoreConTuttiGiorni() {
            for (Giorno g : Giorno.values()) {
                Lezione lezTest = new Lezione(1, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"), g, new Resto(), new Corso(), new Aula());
                assertEquals(g, lezTest.getGiorno());
            }
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'semestre'")
    class SemestreGetterSetterTest {

        @Test
        @DisplayName("getSemestre restituisce 0 per default")
        void testGetSemestreDefault() {
            assertEquals(0, lezione.getSemestre());
        }

        @Test
        @DisplayName("setSemestre e getSemestre funzionano correttamente")
        void testSetGetSemestre() {
            lezione.setSemestre(1);
            assertEquals(1, lezione.getSemestre());

            lezione.setSemestre(2);
            assertEquals(2, lezione.getSemestre());
        }

        @Test
        @DisplayName("setSemestre con valore 0")
        void testSetSemestreZero() {
            lezione.setSemestre(0);
            assertEquals(0, lezione.getSemestre());
        }

        @Test
        @DisplayName("setSemestre con valore negativo")
        void testSetSemestreNegativo() {
            lezione.setSemestre(-1);
            assertEquals(-1, lezione.getSemestre());
        }

        @Test
        @DisplayName("setSemestre con valore alto")
        void testSetSemestreAlto() {
            lezione.setSemestre(Integer.MAX_VALUE);
            assertEquals(Integer.MAX_VALUE, lezione.getSemestre());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'oraInizio'")
    class OraInizioGetterSetterTest {

        @Test
        @DisplayName("getOraInizio restituisce null per default")
        void testGetOraInizioDefault() {
            assertNull(lezione.getOraInizio());
        }

        @Test
        @DisplayName("setOraInizio e getOraInizio funzionano correttamente")
        void testSetGetOraInizio() {
            Time ora = Time.valueOf("09:00:00");
            lezione.setOraInizio(ora);

            assertEquals(ora, lezione.getOraInizio());
        }

        @Test
        @DisplayName("setOraInizio con null è permesso")
        void testSetOraInizioNull() {
            lezione.setOraInizio(Time.valueOf("09:00:00"));
            lezione.setOraInizio(null);

            assertNull(lezione.getOraInizio());
        }

        @Test
        @DisplayName("Modifica sequenziale dell'ora di inizio")
        void testModificaSequenzialeOraInizio() {
            lezione.setOraInizio(Time.valueOf("08:00:00"));
            assertEquals(Time.valueOf("08:00:00"), lezione.getOraInizio());

            lezione.setOraInizio(Time.valueOf("09:00:00"));
            assertEquals(Time.valueOf("09:00:00"), lezione.getOraInizio());

            lezione.setOraInizio(Time.valueOf("10:00:00"));
            assertEquals(Time.valueOf("10:00:00"), lezione.getOraInizio());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'oraFine'")
    class OraFineGetterSetterTest {

        @Test
        @DisplayName("getOraFine restituisce null per default")
        void testGetOraFineDefault() {
            assertNull(lezione.getOraFine());
        }

        @Test
        @DisplayName("setOraFine e getOraFine funzionano correttamente")
        void testSetGetOraFine() {
            Time ora = Time.valueOf("11:00:00");
            lezione.setOraFine(ora);

            assertEquals(ora, lezione.getOraFine());
        }

        @Test
        @DisplayName("setOraFine con null è permesso")
        void testSetOraFineNull() {
            lezione.setOraFine(Time.valueOf("11:00:00"));
            lezione.setOraFine(null);

            assertNull(lezione.getOraFine());
        }

        @Test
        @DisplayName("Modifica sequenziale dell'ora di fine")
        void testModificaSequenzialeOraFine() {
            lezione.setOraFine(Time.valueOf("10:00:00"));
            assertEquals(Time.valueOf("10:00:00"), lezione.getOraFine());

            lezione.setOraFine(Time.valueOf("11:00:00"));
            assertEquals(Time.valueOf("11:00:00"), lezione.getOraFine());

            lezione.setOraFine(Time.valueOf("12:00:00"));
            assertEquals(Time.valueOf("12:00:00"), lezione.getOraFine());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'giorno'")
    class GiornoGetterSetterTest {

        @Test
        @DisplayName("getGiorno restituisce null per default")
        void testGetGiornoDefault() {
            assertNull(lezione.getGiorno());
        }

        @Test
        @DisplayName("setGiorno e getGiorno funzionano correttamente")
        void testSetGetGiorno() {
            Giorno giorno = Giorno.LUNEDI;
            lezione.setGiorno(giorno);

            assertEquals(giorno, lezione.getGiorno());
        }

        @Test
        @DisplayName("setGiorno con null è permesso")
        void testSetGiornoNull() {
            lezione.setGiorno(Giorno.MARTEDI);
            lezione.setGiorno(null);

            assertNull(lezione.getGiorno());
        }

        @Test
        @DisplayName("setGiorno con tutti i giorni della settimana")
        void testSetGiornoTuttiGiorni() {
            for (Giorno g : Giorno.values()) {
                lezione.setGiorno(g);
                assertEquals(g, lezione.getGiorno());
            }
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'corso'")
    class CorsoGetterSetterTest {

        @Test
        @DisplayName("getCorso restituisce null per default")
        void testGetCorsoDefault() {
            assertNull(lezione.getCorso());
        }

        @Test
        @DisplayName("setCorso e getCorso funzionano correttamente")
        void testSetGetCorso() {
            Corso corso = new Corso("Programmazione");
            lezione.setCorso(corso);

            assertEquals(corso, lezione.getCorso());
        }

        @Test
        @DisplayName("setCorso con null è permesso")
        void testSetCorsoNull() {
            lezione.setCorso(new Corso("Test"));
            lezione.setCorso(null);

            assertNull(lezione.getCorso());
        }

        @Test
        @DisplayName("Modifica sequenziale del corso")
        void testModificaSequenzialeCorso() {
            Corso corso1 = new Corso("Corso 1");
            Corso corso2 = new Corso("Corso 2");
            Corso corso3 = new Corso("Corso 3");

            lezione.setCorso(corso1);
            assertEquals(corso1, lezione.getCorso());

            lezione.setCorso(corso2);
            assertEquals(corso2, lezione.getCorso());

            lezione.setCorso(corso3);
            assertEquals(corso3, lezione.getCorso());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'resto'")
    class RestoGetterSetterTest {

        @Test
        @DisplayName("getResto restituisce null per default")
        void testGetRestoDefault() {
            assertNull(lezione.getResto());
        }

        @Test
        @DisplayName("setResto e getResto funzionano correttamente")
        void testSetGetResto() {
            Resto resto = new Resto();
            lezione.setResto(resto);

            assertEquals(resto, lezione.getResto());
        }

        @Test
        @DisplayName("setResto con null è permesso")
        void testSetRestoNull() {
            lezione.setResto(new Resto());
            lezione.setResto(null);

            assertNull(lezione.getResto());
        }

        @Test
        @DisplayName("Modifica sequenziale del resto")
        void testModificaSequenzialeResto() {
            Resto resto1 = new Resto();
            Resto resto2 = new Resto();

            lezione.setResto(resto1);
            assertEquals(resto1, lezione.getResto());

            lezione.setResto(resto2);
            assertEquals(resto2, lezione.getResto());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'aula'")
    class AulaGetterSetterTest {

        @Test
        @DisplayName("getAula restituisce null per default")
        void testGetAulaDefault() {
            assertNull(lezione.getAula());
        }

        @Test
        @DisplayName("setAula e getAula funzionano correttamente")
        void testSetGetAula() {
            Aula aula = new Aula(1, "Edificio A", "Aula 101");
            lezione.setAula(aula);

            assertEquals(aula, lezione.getAula());
        }

        @Test
        @DisplayName("setAula con null è permesso")
        void testSetAulaNull() {
            lezione.setAula(new Aula());
            lezione.setAula(null);

            assertNull(lezione.getAula());
        }

        @Test
        @DisplayName("Modifica sequenziale dell'aula")
        void testModificaSequenzialeAula() {
            Aula aula1 = new Aula(1, "Edificio A", "Aula 101");
            Aula aula2 = new Aula(2, "Edificio B", "Aula 102");

            lezione.setAula(aula1);
            assertEquals(aula1, lezione.getAula());

            lezione.setAula(aula2);
            assertEquals(aula2, lezione.getAula());
        }
    }

    @Nested
    @DisplayName("Test del Getter per 'id'")
    class IdGetterTest {

        @Test
        @DisplayName("getId restituisce null per default")
        void testGetIdDefault() {
            assertNull(lezione.getId());
        }

        @Test
        @DisplayName("getId dopo costruzione")
        void testGetIdConCostruttore() {
            Lezione lezTest = new Lezione(1, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"), Giorno.LUNEDI, new Resto(), new Corso(), new Aula());

            assertNull(lezTest.getId());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'docenti'")
    class DocentiGetterSetterTest {

        @Test
        @DisplayName("getDocenti restituisce lista non null per default")
        void testGetDocentiDefault() {
            List<Docente> docenti = lezione.getDocenti();

            assertNotNull(docenti);
            assertTrue(docenti.isEmpty());
        }

        @Test
        @DisplayName("setDocenti e getDocenti funzionano correttamente")
        void testSetGetDocenti() {
            List<Docente> docentiNuovi = new ArrayList<>();
            docentiNuovi.add(new Docente());
            docentiNuovi.add(new Docente());

            lezione.setDocenti(docentiNuovi);

            assertEquals(docentiNuovi, lezione.getDocenti());
            assertEquals(2, lezione.getDocenti().size());
        }

        @Test
        @DisplayName("Modifica della lista restituita da getDocenti si riflette sull'oggetto")
        void testModificaListaDocenti() {
            List<Docente> docenti = lezione.getDocenti();
            Docente nuovoDocente = new Docente();
            docenti.add(nuovoDocente);

            assertEquals(1, lezione.getDocenti().size());
            assertTrue(lezione.getDocenti().contains(nuovoDocente));
        }

        @Test
        @DisplayName("Aggiunta multipla di docenti")
        void testAggiuntaMultiplaDocenti() {
            List<Docente> docenti = lezione.getDocenti();
            for (int i = 0; i < 5; i++) {
                docenti.add(new Docente());
            }

            assertEquals(5, lezione.getDocenti().size());
        }

        @Test
        @DisplayName("Rimozione di docenti dalla lista")
        void testRimozionDocenti() {
            List<Docente> docenti = lezione.getDocenti();
            Docente doc1 = new Docente();
            Docente doc2 = new Docente();
            docenti.add(doc1);
            docenti.add(doc2);

            assertEquals(2, lezione.getDocenti().size());

            docenti.remove(doc1);

            assertEquals(1, lezione.getDocenti().size());
            assertTrue(lezione.getDocenti().contains(doc2));
            assertFalse(lezione.getDocenti().contains(doc1));
        }

        @Test
        @DisplayName("setDocenti con null")
        void testSetDocentiNull() {
            lezione.setDocenti(null);

            assertNull(lezione.getDocenti());
        }
    }

    @Nested
    @DisplayName("Test del metodo toString")
    class ToStringTest {

        @Test
        @DisplayName("toString con valori di default")
        void testToStringDefault() {
            String result = lezione.toString();

            assertNotNull(result);
            assertTrue(result.contains("Lezione"));
            assertTrue(result.contains("id="));
            assertTrue(result.contains("semestre="));
        }

        @Test
        @DisplayName("toString con tutti i valori impostati")
        void testToStringConValori() {
            lezione = new Lezione(1, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"), Giorno.LUNEDI, new Resto(), new Corso(), new Aula());
            String result = lezione.toString();

            assertNotNull(result);
            assertTrue(result.contains("Lezione"));
            assertTrue(result.contains("semestre=1"));
        }

        @Test
        @DisplayName("toString non è null o vuoto")
        void testToStringNonVuoto() {
            String result = lezione.toString();

            assertNotNull(result);
            assertFalse(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test di integrazione e scenari complessi")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Creazione completa di una lezione con tutte le proprietà")
        void testCreazioneCompleta() {
            Lezione lezCompleta = new Lezione(1, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"), Giorno.LUNEDI, new Resto(), new Corso("Programmazione"), new Aula(1, "Edificio A", "Aula 101"));

            lezCompleta.getDocenti().add(new Docente());
            lezCompleta.getDocenti().add(new Docente());

            assertEquals(1, lezCompleta.getSemestre());
            assertEquals(Time.valueOf("09:00:00"), lezCompleta.getOraInizio());
            assertEquals(Time.valueOf("11:00:00"), lezCompleta.getOraFine());
            assertEquals(Giorno.LUNEDI, lezCompleta.getGiorno());
            assertNotNull(lezCompleta.getCorso());
            assertNotNull(lezCompleta.getResto());
            assertNotNull(lezCompleta.getAula());
            assertEquals(2, lezCompleta.getDocenti().size());
        }

        @Test
        @DisplayName("Modifica completa di una lezione")
        void testModificaCompleta() {
            lezione = new Lezione(1, Time.valueOf("08:00:00"), Time.valueOf("10:00:00"), Giorno.MARTEDI, new Resto(), new Corso(), new Aula());

            lezione.setSemestre(2);
            lezione.setOraInizio(Time.valueOf("14:00:00"));
            lezione.setOraFine(Time.valueOf("16:00:00"));
            lezione.setGiorno(Giorno.MERCOLEDI);

            assertEquals(2, lezione.getSemestre());
            assertEquals(Time.valueOf("14:00:00"), lezione.getOraInizio());
            assertEquals(Time.valueOf("16:00:00"), lezione.getOraFine());
            assertEquals(Giorno.MERCOLEDI, lezione.getGiorno());
        }

        @Test
        @DisplayName("Reset di tutte le proprietà")
        void testResetProprietà() {
            lezione = new Lezione(1, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"), Giorno.LUNEDI, new Resto(), new Corso(), new Aula());
            lezione.getDocenti().add(new Docente());

            // Reset
            lezione.setSemestre(0);
            lezione.setOraInizio(null);
            lezione.setOraFine(null);
            lezione.setGiorno(null);
            lezione.setResto(null);
            lezione.setCorso(null);
            lezione.setAula(null);
            lezione.setDocenti(new ArrayList<>());

            assertEquals(0, lezione.getSemestre());
            assertNull(lezione.getOraInizio());
            assertNull(lezione.getOraFine());
            assertNull(lezione.getGiorno());
            assertNull(lezione.getResto());
            assertNull(lezione.getCorso());
            assertNull(lezione.getAula());
            assertTrue(lezione.getDocenti().isEmpty());
        }

        @Test
        @DisplayName("Associazione lezione con multiple docenti")
        void testAssociazioneMultipleDocenti() {
            for (int i = 0; i < 10; i++) {
                lezione.getDocenti().add(new Docente());
            }

            assertEquals(10, lezione.getDocenti().size());
        }

        @Test
        @DisplayName("Lezione per ogni giorno della settimana")
        void testLezionePerOgniGiorno() {
            for (Giorno g : Giorno.values()) {
                Lezione lez = new Lezione(1, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"), g, new Resto(), new Corso(), new Aula());
                assertEquals(g, lez.getGiorno());
            }
        }
    }

    @Nested
    @DisplayName("Test dei valori limite e casi speciali")
    class CasiLimiteTest {

        @Test
        @DisplayName("Lezione con ora di inizio e fine uguale")
        void testOraInizioFineUguale() {
            Time ora = Time.valueOf("09:00:00");
            lezione.setOraInizio(ora);
            lezione.setOraFine(ora);

            assertEquals(ora, lezione.getOraInizio());
            assertEquals(ora, lezione.getOraFine());
        }

        @Test
        @DisplayName("Lezione alle 00:00:00")
        void testLezioneAlleZeroZero() {
            Time ora = Time.valueOf("00:00:00");
            lezione.setOraInizio(ora);
            lezione.setOraFine(ora);

            assertEquals(ora, lezione.getOraInizio());
            assertEquals(ora, lezione.getOraFine());
        }

        @Test
        @DisplayName("Lezione alle 23:59:59")
        void testLezioneAlleVentiTre() {
            Time ora = Time.valueOf("23:59:59");
            lezione.setOraInizio(ora);
            lezione.setOraFine(ora);

            assertEquals(ora, lezione.getOraInizio());
            assertEquals(ora, lezione.getOraFine());
        }

        @Test
        @DisplayName("Semestre con valore molto grande")
        void testSemestreValoreLargo() {
            lezione.setSemestre(Integer.MAX_VALUE);

            assertEquals(Integer.MAX_VALUE, lezione.getSemestre());
        }

        @Test
        @DisplayName("Semestre con valore minimo")
        void testSemestreValoreMinimo() {
            lezione.setSemestre(Integer.MIN_VALUE);

            assertEquals(Integer.MIN_VALUE, lezione.getSemestre());
        }

        @Test
        @DisplayName("Lista docenti con molti elementi")
        void testListaDocentiGrande() {
            for (int i = 0; i < 100; i++) {
                lezione.getDocenti().add(new Docente());
            }

            assertEquals(100, lezione.getDocenti().size());
        }

        @Test
        @DisplayName("Lezione senza docenti e senza associazioni")
        void testLezioneMinimale() {
            Lezione lezMin = new Lezione();

            assertNull(lezMin.getId());
            assertNull(lezMin.getOraInizio());
            assertNull(lezMin.getOraFine());
            assertNull(lezMin.getGiorno());
            assertNull(lezMin.getCorso());
            assertNull(lezMin.getResto());
            assertNull(lezMin.getAula());
            assertNotNull(lezMin.getDocenti());
            assertTrue(lezMin.getDocenti().isEmpty());
        }
    }

    @Nested
    @DisplayName("Test delle Named Queries (verifica costanti)")
    class NamedQueriesTest {

        @Test
        @DisplayName("Verifica costanti Named Queries sono definite")
        void testCostantiNamedQueries() {
            assertEquals("Lezione.trovaLezione", Lezione.TROVA_LEZIONE);
            assertEquals("Lezione.trovaLezioneCorso", Lezione.TROVA_LEZIONE_CORSO);
            assertEquals("Lezione.trovaLezioneOre", Lezione.TROVA_LEZIONE_ORE);
            assertEquals("Lezione.trovaLezioneOreGiorno", Lezione.TROVA_LEZIONE_ORE_GIORNO);
            assertEquals("Lezione.trovaLezioneAula", Lezione.TROVA_LEZIONE_AULA);
            assertEquals("Lezione.trovaTutte", Lezione.TROVA_TUTTE);
            assertEquals("Lezione.trovaLezioneCorsoRestoAnno", Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO);
            assertEquals("Lezione.trovaLezioneCorsoRestoAnnoSemestre", Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO_SEMESTRE);
            assertEquals("Lezione.trovaLezioniDocente", Lezione.TROVA_LEZIONI_DOCENTE);
        }

        @Test
        @DisplayName("Costanti Named Queries non sono null")
        void testCostantiNonNull() {
            assertNotNull(Lezione.TROVA_LEZIONE);
            assertNotNull(Lezione.TROVA_LEZIONE_CORSO);
            assertNotNull(Lezione.TROVA_LEZIONE_ORE);
            assertNotNull(Lezione.TROVA_LEZIONE_ORE_GIORNO);
            assertNotNull(Lezione.TROVA_LEZIONE_AULA);
            assertNotNull(Lezione.TROVA_TUTTE);
            assertNotNull(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO);
            assertNotNull(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO_SEMESTRE);
            assertNotNull(Lezione.TROVA_LEZIONI_DOCENTE);
        }

        @Test
        @DisplayName("Costanti Named Queries non sono vuote")
        void testCostantiNonVuote() {
            assertFalse(Lezione.TROVA_LEZIONE.isEmpty());
            assertFalse(Lezione.TROVA_LEZIONE_CORSO.isEmpty());
            assertFalse(Lezione.TROVA_LEZIONE_ORE.isEmpty());
            assertFalse(Lezione.TROVA_LEZIONE_ORE_GIORNO.isEmpty());
            assertFalse(Lezione.TROVA_LEZIONE_AULA.isEmpty());
            assertFalse(Lezione.TROVA_TUTTE.isEmpty());
            assertFalse(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO.isEmpty());
            assertFalse(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO_SEMESTRE.isEmpty());
            assertFalse(Lezione.TROVA_LEZIONI_DOCENTE.isEmpty());
        }
    }
}
