package it.unisa.uniclass.testing.unit.conversazioni.service.dao;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.dao.MessaggioDAO;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.time.LocalDateTime;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class MessaggioDAOTest {

    @Mock
    private EntityManager em;

    @Mock
    private TypedQuery<Messaggio> query;

    @InjectMocks
    private MessaggioDAO dao;

    @Test
    @DisplayName("Trova Messaggio per ID")
    void testTrovaMessaggio() {
        Messaggio m = new Messaggio();
        when(em.createNamedQuery(Messaggio.TROVA_MESSAGGIO, Messaggio.class)).thenReturn(query);
        when(query.setParameter("id", 1L)).thenReturn(query);
        when(query.getSingleResult()).thenReturn(m);

        Messaggio result = dao.trovaMessaggio(1L);
        assertSame(m, result);
    }

    @Test
    @DisplayName("Trova Messaggi Inviati")
    void testTrovaMessaggiInviati() {
        when(em.createNamedQuery(Messaggio.TROVA_MESSAGGI_INVIATI, Messaggio.class)).thenReturn(query);
        when(query.setParameter("matricola", "123")).thenReturn(query);
        when(query.getResultList()).thenReturn(Collections.emptyList());

        List<Messaggio> result = dao.trovaMessaggiInviati("123");
        assertNotNull(result);
    }

    @Test
    @DisplayName("Trova Messaggi Ricevuti")
    void testTrovaMessaggiRicevuti() {
        when(em.createNamedQuery(Messaggio.TROVA_MESSAGGI_RICEVUTI, Messaggio.class)).thenReturn(query);
        when(query.setParameter("matricola", "123")).thenReturn(query);
        when(query.getResultList()).thenReturn(Collections.emptyList());

        dao.trovaMessaggiRicevuti("123");
        verify(em).createNamedQuery(Messaggio.TROVA_MESSAGGI_RICEVUTI, Messaggio.class);
    }

    @Test
    @DisplayName("Trova Messaggi tra due utenti")
    void testTrovaMessaggi() {
        when(em.createNamedQuery(Messaggio.TROVA_MESSAGGI_MESSAGGERI, Messaggio.class)).thenReturn(query);
        when(query.setParameter("autore", "A")).thenReturn(query);
        when(query.setParameter("destinatario", "B")).thenReturn(query);
        when(query.getResultList()).thenReturn(Collections.emptyList());

        dao.trovaMessaggi("A", "B");
        verify(query).getResultList();
    }

    @Test
    @DisplayName("Trova Tutti")
    void testTrovaTutti() {
        when(em.createNamedQuery(Messaggio.TROVA_TUTTI, Messaggio.class)).thenReturn(query);
        when(query.getResultList()).thenReturn(Collections.emptyList());
        dao.trovaTutti();
    }

    @Test
    @DisplayName("Trova Avvisi")
    void testTrovaAvvisi() {
        when(em.createNamedQuery(Messaggio.TROVA_AVVISI, Messaggio.class)).thenReturn(query);
        when(query.getResultList()).thenReturn(Collections.emptyList());
        dao.trovaAvvisi();
    }

    @Test
    @DisplayName("Trova Avvisi Autore")
    void testTrovaAvvisiAutore() {
        when(em.createNamedQuery(Messaggio.TROVA_AVVISI_AUTORE, Messaggio.class)).thenReturn(query);
        when(query.setParameter("autore", "123")).thenReturn(query);
        when(query.getResultList()).thenReturn(Collections.emptyList());
        dao.trovaAvvisiAutore("123");
    }

    @Test
    @DisplayName("Trova Messaggi Data")
    void testTrovaMessaggiData() {
        LocalDateTime dt = LocalDateTime.now();
        when(em.createNamedQuery(Messaggio.TROVA_MESSAGGI_DATA, Messaggio.class)).thenReturn(query);
        when(query.setParameter("dateTime", dt)).thenReturn(query);
        when(query.getResultList()).thenReturn(Collections.emptyList());
        dao.trovaMessaggiData(dt);
    }

    @Test
    @DisplayName("Trova per Topic")
    void testTrovaTopic() {
        Topic t = new Topic();
        when(em.createNamedQuery(Messaggio.TROVA_TOPIC, Messaggio.class)).thenReturn(query);
        when(query.setParameter("topic", t)).thenReturn(query);
        when(query.getResultList()).thenReturn(Collections.emptyList());
        dao.trovaTopic(t);
    }

    // --- TEST BRANCH COVERAGE: AGGIUNGI MESSAGGIO ---

    @Test
    @DisplayName("Aggiungi Messaggio: Nuovo (Persist)")
    void testAggiungiMessaggio_Nuovo() {
        // Mock di un messaggio con ID null (simuliamo un oggetto parziale o usiamo spy)
        // Se non puoi settare id a null (perché è Long object), usa un mock che restituisce null
        Messaggio m = mock(Messaggio.class);
        when(m.getId()).thenReturn(null);

        dao.aggiungiMessaggio(m);

        verify(em).persist(m);
        verify(em, never()).merge(m);
        verify(em).flush();
    }

    @Test
    @DisplayName("Aggiungi Messaggio: Esistente (Merge)")
    void testAggiungiMessaggio_Esistente() {
        Messaggio m = mock(Messaggio.class);
        when(m.getId()).thenReturn(1L);

        dao.aggiungiMessaggio(m);

        verify(em).merge(m);
        verify(em, never()).persist(m);
        verify(em).flush();
    }

    @Test
    @DisplayName("Rimuovi Messaggio")
    void testRimuoviMessaggio() {
        Messaggio m = new Messaggio();
        dao.rimuoviMessaggio(m);
        verify(em).remove(m);
    }
}