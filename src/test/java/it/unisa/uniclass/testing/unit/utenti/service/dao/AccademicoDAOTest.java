package it.unisa.uniclass.testing.unit.utenti.service.dao;

import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.service.dao.AccademicoDAO;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test Unitario per AccademicoDAO.
 */
@ExtendWith(MockitoExtension.class)
class AccademicoDAOTest {

    @Mock
    private EntityManager em;

    @Mock
    private TypedQuery<Accademico> query;

    @InjectMocks
    private AccademicoDAO accademicoDAO;

    @Test
    @DisplayName("Create: deve chiamare persist")
    void testCreate() {
        Accademico accademico = new Accademico();
        accademicoDAO.create(accademico);
        verify(em, times(1)).persist(accademico);
    }

    @Test
    @DisplayName("Update: deve chiamare merge")
    void testUpdate() {
        Accademico accademico = new Accademico();
        accademicoDAO.update(accademico);
        verify(em, times(1)).merge(accademico);
    }

    /**
     * Test per Branch Coverage su remove: Caso "Attached".
     * L'entità è già nel contesto (contains = true), quindi NON entra nell'if.
     */
    @Test
    @DisplayName("Remove: Entità già nel contesto (Attached)")
    void testRemove_Attached() {
        Accademico accademico = new Accademico();
        when(em.contains(accademico)).thenReturn(true);

        accademicoDAO.remove(accademico);

        // Verifica che merge NON venga chiamato
        verify(em, never()).merge(accademico);
        // Verifica che remove venga chiamato direttamente
        verify(em, times(1)).remove(accademico);
    }

    /**
     * Test per Branch Coverage su remove: Caso "Detached".
     * L'entità non è nel contesto (contains = false), quindi ENTRA nell'if.
     */
    @Test
    @DisplayName("Remove: Entità non nel contesto (Detached)")
    void testRemove_Detached() {
        Accademico accademico = new Accademico();
        Accademico managedAccademico = new Accademico(); // Istanza simulata dal merge

        when(em.contains(accademico)).thenReturn(false);
        when(em.merge(accademico)).thenReturn(managedAccademico);

        accademicoDAO.remove(accademico);

        // Verifica che il merge sia stato chiamato
        verify(em, times(1)).merge(accademico);
        // Verifica che la rimozione avvenga sull'oggetto restituito dal merge
        verify(em, times(1)).remove(managedAccademico);
    }

    @Test
    @DisplayName("FindByRole: Esegue NamedQuery corretta")
    void testFindByRole() {
        Ruolo ruolo = Ruolo.DOCENTE;
        List<Accademico> expectedList = Collections.singletonList(new Accademico());

        // Configurazione Mock
        when(em.createNamedQuery("Accademico.findByRuolo", Accademico.class)).thenReturn(query);
        when(query.setParameter("ruolo", ruolo)).thenReturn(query);
        when(query.getResultList()).thenReturn(expectedList);

        // Esecuzione
        List<Accademico> result = accademicoDAO.findByRole(ruolo);

        // Verifiche
        assertNotNull(result);
        assertFalse(result.isEmpty());
        assertEquals(expectedList, result);
        verify(em).createNamedQuery("Accademico.findByRuolo", Accademico.class);
    }

    @Test
    @DisplayName("FindByRuoloAndDipartimento: Esegue NamedQuery corretta con due parametri")
    void testFindByRuoloAndDipartimento() {
        Ruolo ruolo = Ruolo.STUDENTE;
        String dipartimento = "Informatica";
        List<Accademico> expectedList = Collections.singletonList(new Accademico());

        // Configurazione Mock
        when(em.createNamedQuery("Accademico.findByRuoloAndDip", Accademico.class)).thenReturn(query);
        when(query.setParameter("ruolo", ruolo)).thenReturn(query);
        when(query.setParameter("dipartimento", dipartimento)).thenReturn(query);
        when(query.getResultList()).thenReturn(expectedList);

        // Esecuzione
        List<Accademico> result = accademicoDAO.findByRuoloAndDipartimento(ruolo, dipartimento);

        // Verifiche
        assertEquals(expectedList, result);
    }

    @Test
    @DisplayName("FindAll: Esegue NamedQuery corretta")
    void testFindAll() {
        List<Accademico> expectedList = Collections.singletonList(new Accademico());

        when(em.createNamedQuery("Accademico.findAll", Accademico.class)).thenReturn(query);
        when(query.getResultList()).thenReturn(expectedList);

        List<Accademico> result = accademicoDAO.findAll();

        assertEquals(expectedList, result);
    }

    @Test
    @DisplayName("FindByMatricola: Restituisce singolo risultato")
    void testFindByMatricola() {
        String matricola = "0512101234";
        Accademico expected = new Accademico();
        expected.setMatricola(matricola);

        when(em.createNamedQuery("Accademico.findByMatricola", Accademico.class)).thenReturn(query);
        when(query.setParameter("matricola", matricola)).thenReturn(query);
        when(query.getSingleResult()).thenReturn(expected);

        Accademico result = accademicoDAO.findByMatricola(matricola);

        assertNotNull(result);
        assertEquals(matricola, result.getMatricola());
    }
}