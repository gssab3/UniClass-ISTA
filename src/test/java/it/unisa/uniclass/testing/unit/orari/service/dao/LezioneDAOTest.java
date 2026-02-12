package it.unisa.uniclass.testing.unit.orari.service.dao;

import it.unisa.uniclass.orari.model.Giorno;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.service.dao.LezioneDAO;
import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.Time;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class LezioneDAOTest {

    @Mock
    private EntityManager em;

    @Mock
    private TypedQuery<Lezione> query;

    @InjectMocks
    private LezioneDAO dao;

    // --- TEST METODI DI RICERCA (SELECT) ---

    @Test
    @DisplayName("Trova Lezione per ID")
    void testTrovaLezione() {
        Lezione l = new Lezione();
        when(em.find(Lezione.class, 1L)).thenReturn(l);
        assertSame(l, dao.trovaLezione(1L));
    }

    @Test
    @DisplayName("Trova Lezioni Corso")
    void testTrovaLezioniCorso() {
        setupQueryMock(Lezione.TROVA_LEZIONE_CORSO);
        List<Lezione> result = dao.trovaLezioniCorso("Informatica");
        assertNotNull(result);
        verify(query).setParameter("nomeCorso", "Informatica");
    }

    @Test
    @DisplayName("Trova Lezioni per Ore")
    void testTrovaLezioniOre() {
        setupQueryMock(Lezione.TROVA_LEZIONE_ORE);
        Time start = Time.valueOf("09:00:00");
        Time end = Time.valueOf("11:00:00");

        dao.trovaLezioniOre(start, end);

        verify(query).setParameter("oraInizio", start);
        verify(query).setParameter("oraFine", end);
    }

    @Test
    @DisplayName("Trova Lezioni per Ore e Giorno")
    void testTrovaLezioniOreGiorno() {
        setupQueryMock(Lezione.TROVA_LEZIONE_ORE_GIORNO);
        Time start = Time.valueOf("09:00:00");
        Time end = Time.valueOf("11:00:00");

        dao.trovaLezioniOreGiorno(start, end, Giorno.LUNEDI);

        verify(query).setParameter("giorno", Giorno.LUNEDI);
    }

    @Test
    @DisplayName("Trova Lezioni Aule")
    void testTrovaLezioniAule() {
        setupQueryMock(Lezione.TROVA_LEZIONE_AULA);
        dao.trovaLezioniAule("F1");
        verify(query).setParameter("nome", "F1");
    }

    @Test
    @DisplayName("Trova Tutte")
    void testTrovaTutte() {
        when(em.createNamedQuery(Lezione.TROVA_TUTTE, Lezione.class)).thenReturn(query);
        when(query.getResultList()).thenReturn(Collections.emptyList());
        dao.trovaTutte();
        verify(em).createNamedQuery(Lezione.TROVA_TUTTE, Lezione.class);
    }

    @Test
    @DisplayName("Trova Lezioni Filtri (Corso, Resto, Anno)")
    void testTrovaLezioniFiltriBase() {
        setupQueryMock(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO);

        // Mocking chain per parametri misti (long e int)
        when(query.setParameter(anyString(), anyLong())).thenReturn(query);
        when(query.setParameter(anyString(), anyInt())).thenReturn(query);

        dao.trovaLezioniCorsoLaureaRestoAnno(1L, 2L, 2023);

        verify(query).setParameter("corsoLaureaId", 1L);
        verify(query).setParameter("restoId", 2L);
        verify(query).setParameter("annoId", 2023);
    }

    @Test
    @DisplayName("Trova Lezioni Filtri Completi (+ Semestre)")
    void testTrovaLezioniFiltriCompleti() {
        setupQueryMock(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO_SEMESTRE);

        when(query.setParameter(anyString(), anyLong())).thenReturn(query);
        when(query.setParameter(anyString(), anyInt())).thenReturn(query);

        dao.trovaLezioniCorsoLaureaRestoAnnoSemestre(1L, 2L, 2023, 1);

        verify(query).setParameter("semestre", 1);
    }

    @Test
    @DisplayName("Trova Lezioni Docente")
    void testTrovaLezioniDocente() {
        setupQueryMock(Lezione.TROVA_LEZIONI_DOCENTE);
        dao.trovaLezioniDocente("Rossi");
        verify(query).setParameter("nomeDocente", "Rossi");
    }

    @Test
    @DisplayName("Aggiungi Lezione")
    void testAggiungiLezione() {
        Lezione l = new Lezione();
        dao.aggiungiLezione(l);
        verify(em).persist(l);
    }

    // --- TEST CRITICI PER BRANCH COVERAGE SU REMOVE ---

    @Test
    @DisplayName("Rimuovi Lezione: Con relazioni (Accademici) e Detached")
    void testRimuoviLezione_WithRelations_Detached() {
        // Arrange
        Lezione l = new Lezione();
        Lezione mergedLezione = new Lezione(); // Simulacro dell'oggetto post-merge

        Accademico acc1 = mock(Accademico.class);
        List<Lezione> lezioniDiAcc1 = new ArrayList<>();
        lezioniDiAcc1.add(l);
        when(acc1.getLezioni()).thenReturn(lezioniDiAcc1);

        List<Accademico> accademici = new ArrayList<>();
        accademici.add(acc1);
        l.setAccademici(accademici);

        // Branch Detached: contains restituisce false
        when(em.contains(l)).thenReturn(false);
        when(em.merge(l)).thenReturn(mergedLezione);

        // Act
        dao.rimuoviLezione(l);

        // Assert
        // 1. Verifica che la lezione sia stata rimossa dalla lista dell'accademico
        assertFalse(lezioniDiAcc1.contains(l));

        // 2. Verifica che l'accademico sia stato aggiornato (merge)
        verify(em).merge(acc1);

        // 3. Verifica che sia stato fatto il merge della lezione (perché detached)
        verify(em).merge(l);

        // 4. Verifica la rimozione finale sull'oggetto gestito
        verify(em).remove(mergedLezione);
    }

    @Test
    @DisplayName("Rimuovi Lezione: Senza relazioni e Attached")
    void testRimuoviLezione_NoRelations_Attached() {
        // Arrange
        Lezione l = new Lezione();
        l.setAccademici(null); // Forza ramo if(getAccademici != null) a false

        // Branch Attached: contains restituisce true
        when(em.contains(l)).thenReturn(true);

        // Act
        dao.rimuoviLezione(l);

        // Assert
        // Non deve provare a fare merge degli accademici
        verify(em, never()).merge(any(Accademico.class));

        // Non deve fare merge della lezione (è già attached)
        verify(em, never()).merge(l);

        // Deve rimuovere direttamente
        verify(em).remove(l);
    }

    // --- Helper per evitare boilerplate code nei test delle query ---
    private void setupQueryMock(String queryName) {
        when(em.createNamedQuery(eq(queryName), eq(Lezione.class))).thenReturn(query);
        // Configura il mock per supportare il chaining dei setParameter
        lenient().when(query.setParameter(anyString(), any())).thenReturn(query);
        lenient().when(query.getResultList()).thenReturn(new ArrayList<>());
    }
}